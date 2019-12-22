{-# LANGUAGE TupleSections #-}
module Compiler.ILExprTransformer where

import AbsLatte as A
import Compiler.ILTransformerCommon
import Llvm
import TypeChecker.TypeCheckUtils as TCU
import Control.Monad
import Unique (getUnique)
import Common.ASTUtils (extract)
import System.IO.Unsafe (unsafePerformIO)

number64::Integer -> LlvmVar
number64 a = LMLitVar (LMIntLit a i64)

transformRExpr:: Expr TCU.Type -> StmtWriter LlvmVar

transformRExpr (ELitInt _ v) = return ( LMLitVar $ LMIntLit v i32)

transformRExpr ELitTrue{} = return (LMLitVar $ LMIntLit 1 i1)
transformRExpr ELitFalse{} = return (LMLitVar $ LMIntLit 0 i1)

transformRExpr (EString _ nv) = do
  v <- lift $ lift $ createConstString nv
  sAssign i8Ptr (GetElemPtr True (pVarLift v) [number 0, number 0])

transformRExpr (ENull t _) = return $ LMLitVar $ LMNullLit $ valTType t

transformRExpr (EAnd t v1 v2) = transformBinaryOp t v1 v2 LM_MO_And
transformRExpr (EOr t v1 v2) = transformBinaryOp t v1 v2 LM_MO_Or

transformRExpr (EAdd t v1 Plus{} v2) = transformBinaryOp t v1 v2 LM_MO_Add
transformRExpr (EAdd t v1 Minus{} v2) = transformBinaryOp t v1 v2 LM_MO_Sub
transformRExpr (EMul t v1 Times{} v2) = transformBinaryOp t v1 v2 LM_MO_Mul
transformRExpr (EMul t v1 Div{} v2) = transformBinaryOp t v1 v2 LM_MO_SDiv
transformRExpr (EMul t v1 Mod{} v2) = transformBinaryOp t v1 v2 LM_MO_SRem

transformRExpr (ERel t v1 LTH{} v2) = transformBinaryCmp t v1 v2 LM_CMP_Slt
transformRExpr (ERel t v1 LE{} v2) = transformBinaryCmp t v1 v2 LM_CMP_Sle
transformRExpr (ERel t v1 GTH{} v2) = transformBinaryCmp t v1 v2 LM_CMP_Sgt
transformRExpr (ERel t v1 GE{} v2) = transformBinaryCmp t v1 v2 LM_CMP_Sge 
transformRExpr (ERel t v1 EQU{} v2) = transformBinaryCmp t v1 v2 LM_CMP_Eq
transformRExpr (ERel t v1 NE{} v2) = transformBinaryCmp t v1 v2 LM_CMP_Ne 

transformRExpr (Neg t v1) = transformRExpr (EMul t (ELitInt t (-1)) (Times t) v1)
transformRExpr (Not t v1) = do
  v <- transformRExpr v1
  sAssign i1 (LlvmOp LM_MO_Sub (litNum 1 i1) v)

transformRExpr (EVar t (Ident name)) = do
  hasLocal <- hasLocalVar name
  if hasLocal then getLocalVar name -- redukcja loadów, przed usunięciem store'ów
  else do
        v <- sGetVar name
        let vType = valTType t
        case getVarType v of
          (LMPointer t) | t == vType -> sAssign vType (Load v) >>= (\v -> sAddLocalVar name v Read) >> getLocalVar name
          t | t == vType -> return v
          t -> sAssign vType (Cast LM_Bitcast v vType)

transformRExpr e@(EFldNoAcc t obj num) = do
  n1 <- transformLExpr e
  sAssign (pLower $ getVarType n1) (Load n1)

transformRExpr e@(EArrAcc t a ind) = do
  n1 <- transformLExpr e
  sAssign (valTType t) (Load n1)

transformRExpr (ENewObj t@(TCU.Class name) _) = do
  let pt@(LMPointer nt) = valTType t
  virtArrGlobal <- sGetVar $ "virt_" ++ name
  let virtArrGlobalPtr = pVarLift virtArrGlobal --TODO Czy to nie powinno być w jednej funkcji zamiast za każdym razem powtarzać ?
  sizeCalcOne      <- calcStructSize nt
  tmp1             <- sAssign i8Ptr(Call StdCall malloc [sizeCalcOne] [])
  addStmt $           callMemset tmp1 sizeCalcOne
  nVar             <- sAssign pt (Cast LM_Bitcast tmp1 pt)
  virtPtr          <- sAssign (LMPointer $ LMPointer i8Ptr) (GetElemPtr True nVar [number 0, number 0])
  virtArrToBytePtr <- sAssign (LMPointer i8Ptr) (Cast LM_Bitcast virtArrGlobalPtr (LMPointer i8Ptr))
  addStmt $           Store virtArrToBytePtr virtPtr
  return nVar

transformRExpr e@(ENewArr _ t size) = --do
  transformLExpr e

transformRExpr e@(EVirtCall rt obj num args) = do
  let rtt = valTType rt
  argsV <- mapM transformRExpr args
  let argTypes = map getVarType argsV
  objPtr <- transformRExpr obj
  let fType = LMFunction (LlvmFunctionDecl (mkfs "") Internal CC_Fastcc rtt FixedArgs ((getVarType objPtr,[]) : map (,[]) argTypes) Nothing)
  tmp <- sNewVar i8Ptr
  let (LMNLocalVar n _) = tmp
  let fF = LMLocalVar (getUnique n) $ LMPointer fType
  val <- sNewVar rtt
  vTablePtrPtr <- sAssign (LMPointer $ LMPointer i8Ptr) (GetElemPtr True objPtr [number 0, number 0])
  vTablePtr    <- sAssign (LMPointer i8Ptr) (Load vTablePtrPtr)
  fPtrAddr     <- sAssign (LMPointer i8Ptr) (GetElemPtr True vTablePtr [number num])
  fPtr         <- sAssign i8Ptr (Load fPtrAddr)
  fPtrFin      <- tryLocal fF (Cast LM_Bitcast fPtr (LMPointer fType))
  addStmt $ (if rt /= TCU.Void then Assignment val else Llvm.Expr) (Call StdCall fPtrFin (objPtr: argsV) [])
  return val

transformRExpr (EApp r (EVar fType (Ident fName)) args) = do
  vs <- mapM transformRExpr args
  fVar <- sGetVar fName
  nValue <- sNewVar $ valTType r
  let (TCU.Fun _ argsExpTypes) = fType
  let realTypes = map extract args
  adjusted <- sequence $ zipWith3 toCorrectType realTypes argsExpTypes vs
  addStmt $ (if r == TCU.Void then Llvm.Expr else Assignment nValue) (Call StdCall fVar adjusted [])
  return nValue
  where toCorrectType t exp v | t == exp = return v
        toCorrectType t exp v = sAssign (valTType exp) (Cast LM_Bitcast v (valTType exp)) -- może wskazywac na podklasę

transformRExpr e = error $ "Not supported " ++ show e

number::Integer -> LlvmVar
number n = LMLitVar (LMIntLit n i32)


transformLExpr::Expr TCU.Type -> StmtWriter LlvmVar
transformLExpr (EVar t (Ident name)) = sGetVar name

transformLExpr (EFldNoAcc t obj num) = do
  v <- transformRExpr obj
  sAssign (LMPointer $ valTType t) (GetElemPtr True v [number 0, number num])

transformLExpr (EArrAcc t a ind) = do
  a1 <- transformRExpr a
  ind1 <- transformRExpr ind
  n1 <- sAssign (LMPointer $ LMPointer $ valTType t) (GetElemPtr True a1 [number 0, number 1])
  n2 <- sAssign (LMPointer $ valTType t) (Load n1)
  sAssign (LMPointer $ valTType t) (GetElemPtr True n2 [ind1])

transformLExpr (ENewArr _ t size) = do
  n1 <- transformRExpr size
  let elemType = valType t
  let arrayType = LMPointer elemType
  let structType = map2Type (A.Array None t)
  let zero = number 0
  sizeCalcOne <- calcStructSize elemType
  sext        <- sAssign i64 (Cast Llvm.LM_Sext n1 i64)
  allSize     <- sAssign i64 (LlvmOp LM_MO_Mul sizeCalcOne sext)
  tmp1        <- sAssign i8Ptr (Call StdCall malloc [number64 8] [])
  addStmt $ callMemset tmp1 (number64 8)
  arrPtr      <- sAssign (LMPointer structType) (Cast LM_Bitcast tmp1 (LMPointer structType))
  sizePtr     <- sAssign (LMPointer i32) (GetElemPtr True arrPtr [zero, zero])
  addStmt $ Store n1 sizePtr
  tmp2        <- sAssign i8Ptr (Call StdCall malloc [allSize] [])
  addStmt $ callMemset tmp2 allSize
  tmpContPtr  <- sAssign (LMPointer elemType) (Cast LM_Bitcast tmp2 (LMPointer elemType))
  contentPtr  <- sAssign (LMPointer $ LMPointer elemType) (GetElemPtr True arrPtr [zero, number 1])
  addStmt $ Store tmpContPtr contentPtr
  return arrPtr

transformLExpr e =  sNewVar $ mapTypes $ extract e --Tu będą błędy :)


transformBinaryOp::TCU.Type -> Expr TCU.Type -> Expr TCU.Type ->LlvmMachOp -> StmtWriter LlvmVar
transformBinaryOp rt v1 v2 op = do
  v1 <- transformRExpr v1
  v2 <- transformRExpr v2
  let expr = LlvmOp op v1 v2
  if isSimplifiable expr then return $ simplifyExpr expr
  else sAssign (valTType rt) expr


transformBinaryCmp::TCU.Type -> Expr TCU.Type -> Expr TCU.Type ->LlvmCmpOp -> StmtWriter LlvmVar
transformBinaryCmp rt v1 v2 op = do
  let bToLit a = return $ if a then litNum 1 i1 else litNum 0 i1
  v1 <- transformRExpr v1
  v2 <- transformRExpr v2
  let expr = Compare op v1 v2
  if isSimplifiable expr then return $ simplifyExpr expr
  else sAssign (valTType rt) expr


calcStructSize::LlvmType -> StmtWriter LlvmVar
calcStructSize t | t == i1 = return $ number64 1
calcStructSize t | t == i8 = return $ number64 1
calcStructSize t | t == i32 = return $ number64 4
calcStructSize t | t == i64 = return $ number64 8
calcStructSize (LMPointer _) = return $ number64 4 --TODO czy zawsze ? ...
calcStructSize elemType = do
  let elemPtrType = LMPointer elemType
  sizeCalcPtr <- sAssign elemPtrType (GetElemPtr False (LMLitVar (LMNullLit elemPtrType)) [number 1])
  sAssign i64 (Cast LM_Ptrtoint sizeCalcPtr i64)
  