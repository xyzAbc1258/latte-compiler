{-# LANGUAGE TupleSections #-}
module Compiler.ILExprTransformer where

import AbsLatte as A
import Compiler.ILTransformerCommon
import Llvm
import TypeChecker.TypeCheckUtils as TCU
import Control.Monad
import Unique (getUnique)
import Common.ASTUtils (extract)

transformRExpr:: Expr TCU.Type -> Translator ([LlvmStatement], LlvmVar)

transformRExpr (ELitInt _ v) = return ([], LMLitVar $ LMIntLit v i32)

transformRExpr ELitTrue{} = return ([], LMLitVar $ LMIntLit 1 i1)
transformRExpr ELitFalse{} = return ([], LMLitVar $ LMIntLit 0 i1)

transformRExpr (EString _ v) = return ([], LMLitVar $ LMNullLit i8Ptr)

transformRExpr (ENull t _) = return ([], LMLitVar $ LMNullLit $ mapTypes t)

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
transformRExpr (Not t v1) = transformRExpr (EAdd t (ELitInt t 1) (Minus t) v1)

transformRExpr (EVar t (Ident name)) = do
  v <- getVar name
  let vType = valTType t
  newOne <- newVar vType
  case getVarType v of
    (LMPointer t) | t == vType -> return ([Assignment newOne (Load v)], newOne)
    t | t == vType -> return ([],v)
    t -> return ([],v) --error $ "Wrong expression type: "

transformRExpr e@(EFldNoAcc t obj num) = do
  (s, n1) <- transformLExpr e
  n2 <- newVar $ valTType t
  let assign = Assignment n2 (Load n1)
  return (s ++ [assign], n2)

transformRExpr e@(EArrAcc t a ind) = do
  (s1, n1) <- transformLExpr e
  n2 <- newVar $ valTType t
  let assign = Assignment n2 (Load n1)
  return (s1 ++ [assign], n2)

transformRExpr (ENewObj t@(TCU.Class name) _) = do
  let pt@(LMPointer nt) = valTType t
  nVar <- newVar pt
  virtPtr <- newVar $ LMPointer $ LMPointer $ i8Ptr
  virtArr <- getVar $ "virt_" ++ name
  let virtArrCheat = pVarLift virtArr
  virtArrToBytePtr <- newVar (LMPointer i8Ptr)
  return ([
            Assignment nVar (Alloca nt 1),
            Assignment virtPtr (GetElemPtr True nVar [number 0, number 0]),
            Assignment virtArrToBytePtr (Cast LM_Bitcast virtArrCheat (LMPointer i8Ptr)),
            Store virtArrToBytePtr virtPtr
            ], nVar)

transformRExpr e@(ENewArr _ t size) = --do
  transformLExpr e
  --(s, v) <- transformLExpr e
  --let LMPointer nt = getVarType v
  --nVar <- newVar nt
  --return (s ++ [Assignment nVar (Load v)], nVar)

transformRExpr e@(EVirtCall rt obj num args) = do
  let rtt = valTType rt
  (argsss, argsV) <- mapAndUnzipM transformRExpr args
  let argTypes = map getVarType argsV
  (s1, objPtr) <- transformRExpr obj
  let fType = LMFunction (LlvmFunctionDecl (mkfs "") Internal CC_Fastcc rtt FixedArgs ((getVarType objPtr,[]) : map (,[]) argTypes) Nothing)
  vTablePtrPtr <- newVar $ LMPointer $ LMPointer i8Ptr
  vTablePtr <- newVar $ LMPointer i8Ptr
  fPtrAddr <- newVar $ LMPointer i8Ptr
  fPtr <- newVar i8Ptr
  tmp <- newVar i8Ptr
  let (LMNLocalVar n _) = tmp
  let fF = LMLocalVar (getUnique n) $ LMPointer fType -- newVar $ LMPointer fType
  val <- newVar rtt
  let stmts = [
                Assignment vTablePtrPtr (GetElemPtr True objPtr [number 0, number 0]),
                Assignment vTablePtr (Load vTablePtrPtr),
                Assignment fPtrAddr (GetElemPtr True vTablePtr [number num]),
                Assignment fPtr (Load fPtrAddr),
                Assignment fF (Cast LM_Bitcast fPtr (LMPointer fType)),
                Assignment val (Call StdCall fF (objPtr: argsV) [])
              ]
  return ((argsss >>= id) ++ s1 ++ stmts, val)


transformRExpr (EApp r (EVar _ (Ident fName)) args) = do
  (argss, vs) <- mapAndUnzipM transformRExpr args
  fVar <- getVar fName
  nValue <- newVar $ mapTypes r
  let ass = Assignment nValue (Call StdCall fVar vs [])
  return ((argss >>= id) ++ [ass], nValue)

number::Integer -> LlvmVar
number n = LMLitVar (LMIntLit n i32)


transformLExpr::Expr TCU.Type -> Translator ([LlvmStatement], LlvmVar)
transformLExpr (EVar t (Ident name)) = ([],) <$> getVar name

transformLExpr (EFldNoAcc t obj num) = do
  (s, v) <- transformRExpr obj
  n1 <- newVar $ LMPointer $ valTType t
  let getPtr = Assignment n1 (GetElemPtr True v [number 0, number num])
  return (s ++ [getPtr], n1)

transformLExpr (EArrAcc t a ind) = do
  (s1, a1) <- transformRExpr a
  (s2, ind1) <- transformRExpr ind
  n1 <- newVar $ LMPointer $ LMPointer $ valTType t
  n2 <- newVar $ LMPointer $ valTType t
  n3 <- newVar $ LMPointer $ valTType t
  let ptr = [
              Assignment n1 (GetElemPtr True a1 [number 0, number 1]),
              Assignment n2 (Load n1),
              Assignment n3 (GetElemPtr True n2 [ind1])
            ]
  return (s1 ++ s2 ++ ptr, n3)


transformLExpr (ENewArr _ t size) = do (s1, n1) <- transformRExpr size
                                       let elemType = valType t
                                       let arrayType = LMPointer elemType
                                       let structType = map2Type (A.Array None t)
                                       arrPtr <- newVar (LMPointer structType)
                                       sizePtr <- newVar (LMPointer i32)
                                       tmpContPtr <- newVar (LMPointer elemType)
                                       let zero = number 0
                                       contentPtr <- newVar (LMPointer $ LMPointer elemType)
                                       val <- newVar structType
                                       let stmts
                                             = [Assignment arrPtr (Alloca structType 1),
                                                Assignment sizePtr (GetElemPtr True arrPtr [zero, zero]),
                                                Store n1 sizePtr,
                                                Assignment tmpContPtr (Alloca elemType 1),
                                                Assignment contentPtr (GetElemPtr True arrPtr [zero, number 1]),
                                                Store tmpContPtr contentPtr]
                                       return (s1 ++ stmts, arrPtr)

transformLExpr e = do
  n <- newVar $ mapTypes $ extract e
  return ([], n)

transformBinaryOp::TCU.Type -> Expr TCU.Type -> Expr TCU.Type ->LlvmMachOp -> Translator ([LlvmStatement], LlvmVar)
transformBinaryOp = transformGenBin LlvmOp

transformBinaryCmp::TCU.Type -> Expr TCU.Type -> Expr TCU.Type ->LlvmCmpOp -> Translator ([LlvmStatement], LlvmVar)
transformBinaryCmp = transformGenBin Compare

transformGenBin::(a -> LlvmVar -> LlvmVar -> LlvmExpression) -> TCU.Type -> Expr TCU.Type -> Expr TCU.Type -> a -> Translator ([LlvmStatement], LlvmVar)
transformGenBin oper rt v1 v2 op = do
  (s1, v1) <- transformRExpr v1
  (s2, v2) <- transformRExpr v2
  nVar <- newVar $ mapTypes rt
  let assign = Assignment nVar (oper op v1 v2)
  return (s1 ++ s2 ++ [assign], nVar)