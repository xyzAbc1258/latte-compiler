module TypeChecker.TypeCheckerExpr where

import AbsLatte
import Control.Applicative(liftA2)
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State
import TypeChecker.TypeCheckCommon as TCC
import TypeChecker.TypeCheckUtils as TCC
import Data.Maybe
import Data.List
import Common.Utils
import Common.ASTUtils
import Common.ASTModifier as ASTM
import TypeChecker.TypeUtils
import qualified Data.Map as M
import qualified Common.Graphs as Gr
import Control.Lens((&))
import Data.Tuple(swap)
import TypeChecker.ExprSimplification(simplifyExpr)

checkExpr::(Positionable a) => Expr a -> TypeChecker (Expr TCC.AllocType)
checkExpr e = withPos (extract e) >> _checkExpr e

_checkExpr::(Positionable a) => Expr a -> TypeChecker (Expr TCC.AllocType)
_checkExpr (EVar pos (Ident x)) = do
  d <- getInScope Global (varL x)
  when (isNothing d) $ throwPosError $ "Variable " ++ x ++ " is undefined"
  case fromJust d of
    Instance _ t -> do
                      cType <- varType . fromJust <$> getInScope Global (varL thisName)
                      let (TCC.Class cName) = cType
                      cTypeI <- fromJust <$> getInScope Global (classI cName)
                      return $ EFldNoAcc (LValue t) (EVar (RValue cType) (Ident thisName)) (_varNameMapping cTypeI M.! x)
    LocalVar _ t -> do
                      newName <- getInScope Global $ varMappingL x
                      let finalName = newName <|> Just x
                      return $ EVar (LValue t) (Ident (fromJust finalName))

_checkExpr (ELitInt _ i) = return $ ELitInt (RValue TCC.Int) i
_checkExpr (ELitTrue _) = return $ ELitTrue (RValue TCC.Bool)
_checkExpr (ELitFalse _) = return $ ELitFalse (RValue TCC.Bool)

_checkExpr (ENewObj pos t@(AbsLatte.Class _ (Ident a))) = do
  c <- getInScope Global (classI a)
  unless (isJust c) $ throwPosError $ "Class " ++ a ++ " doesnt exists"
  return $ EApp (LValue $ TCC.Class a) (EVar (RValue $ TCC.Fun (TCC.Class a) []) (Ident $ initFunctionName a)) []

_checkExpr (EFldAcc pos obj fld@(Ident fldName)) = do
  objExpr <- checkExpr obj
  case getType (extract objExpr) of
    TCC.Array _ -> do unless (fldName == "length") $ throwPosError "Array doesnt have any other field than length"
                      return $ EFldNoAcc (RValue TCC.Int) objExpr 0
    TCC.Class cname -> do cInfo <- fromJust <$> getInScope Global (classI cname)
                          let fldType = _components cInfo M.!? fldName
                          unless (isJust fldType) $ throwPosError $ "Class " ++ cname ++ " doesn't have member " ++ fldName
                          let fldNo = TCC._varNameMapping cInfo M.! fldName
                          return $ EFldNoAcc (LValue $ fromJust fldType) objExpr fldNo
    t -> throwPosError $ "Type " ++ show t ++ " doesnt have any field!!!"

_checkExpr (EApp pos (EVar _ (Ident fName)) args) = do
  fType <- getInScope Global (functionI fName)
  unless (isJust fType) $ throwPosError $ "Function " ++ fName ++ " is not defined"
  let func = fromJust fType
  case func of
    TCC.InstanceFunc {} -> do
                        let this = EVar pos (Ident thisName)
                        let nExpr = EApp pos (EFldAcc pos this (Ident fName)) args
                        checkExpr nExpr
    TCC.FunctionInfo _ rType tArgs -> do
                        unless (length tArgs == length args) $ wrongArgsNumber (length tArgs) (length args)
                        argsExpr <- mapM checkExpr args
                        zipWithM_ expectsTypeAE tArgs argsExpr
                        let retAllocType =case rType of
                                            (TCC.Class _) -> RValue
                                            (TCC.Array _) -> RValue
                                            _ -> LValue
                        return $ EApp (retAllocType rType) (EVar (RValue (TCC.Fun rType tArgs)) (Ident fName)) argsExpr


_checkExpr (EApp pos (EFldAcc _ obj (Ident fName)) args) = do
  objExpr <- checkExpr obj
  case getType $ extract objExpr of
    thisType@(TCC.Class cName) -> do
                        cInfo <- fromJust <$> getInScope Global (classI cName)
                        let fNumber = _fNameMapping (_vtable cInfo) M.! fName
                        let maybeFType = _components cInfo M.!? fName
                        unless (maybe False isFunc maybeFType) $ throwPosError $ "Class " ++ cName ++ " doesn't have function " ++ fName
                        let (TCC.Fun rType tArgs) = fromJust maybeFType
                        unless (length tArgs == length args) $ wrongArgsNumber (length tArgs) (length args)
                        argsExpr <- mapM checkExpr args
                        zipWithM_ expectsTypeAE tArgs argsExpr
                        let retAllocType =case rType of
                                             (TCC.Class _) -> RValue
                                             (TCC.Array _) -> RValue
                                             _ -> LValue
                        if wasFOverriden fName cInfo then return $ EVirtCall (retAllocType rType) objExpr fNumber argsExpr
                        else do
                              let (fF, ofc) = _fMapping (_vtable cInfo) M.! fNumber
                              let origClass = TCC.Class ofc
                              return $ EApp (retAllocType rType) (EVar (RValue (TCC.Fun rType (origClass : tArgs))) (Ident fF)) (objExpr : argsExpr)
    _ -> throwPosError "Cannot call function on object which is not a class"

_checkExpr (ENewArr pos aType length) = do
  lengthExpr <- checkExpr length
  expectsTypeAE TCC.Int lengthExpr
  let mType = mapType aType
  typeExists mType
  return $ ENewArr (LValue $ TCC.Array mType) (insertNoneType aType) lengthExpr


_checkExpr (EArrAcc pos arr index) = do
  eInd <- checkExpr index
  expectsTypeAE TCC.Int eInd
  aExpr <- checkExpr arr
  case getType $ extract aExpr of
    TCC.Array t -> return $ EArrAcc (LValue t) aExpr eInd
    t -> throwPosError $ "Expected expression of type array, got: " ++ show t

_checkExpr (EString _ s) = do
  let ns = if null s || head s /= '"' then s else init (tail s) -- coś nie tak z parsowaniem
  return $ EString (RValue TCC.Str) ns

_checkExpr (Neg pos a) = do
  inner <- checkExpr a
  expectsTypeAE TCC.Int inner
  simplifyExpr $ Neg (RValue TCC.Int) inner

_checkExpr (Not pos a) = do
  inner <- checkExpr a
  expectsTypeAE TCC.Bool inner
  simplifyExpr $ Not (RValue TCC.Bool) inner

_checkExpr (EMul pos op1 opr op2) = withPos pos >> binOpCheckTrio op1 op2 TCC.Int (\t e1 -> EMul t e1 (insertNoneType opr))

_checkExpr(EAdd pos  op1 p@(Plus _) op2) = do
  e1 <- checkExpr op1
  e2 <- checkExpr op2
  let t1 = getType $ extract e1
  let t2 = getType $ extract e2
  unless ((t1,t2) `elem` [(TCC.Int, TCC.Int), (TCC.Str, TCC.Str)]) $ throwPosError "Couldnt deduce operand types"
  simplifyExpr $ EAdd (RValue t1) e1 (insertNoneType p) e2

_checkExpr (EAdd pos op1 opr@Minus{} op2) = withPos pos >> binOpCheckTrio op1 op2 TCC.Int (\t e1 -> EAdd t e1 (insertNoneType opr))

_checkExpr (ERel p op1 opr op2)  | case opr of EQU{} -> True ; NE{} -> True ; _ -> False ; = do
  e1 <- checkExpr op1
  e2 <- checkExpr op2
  let t1 = getType $ extract e1
  let t2 = getType $ extract e2
  areTypesOk <- case (t1, t2) of
    (_,_) | t1 == t2 -> return True
    (TCC.Class c1, TCC.Class c2) -> hasCommonSuperClass c1 c2
    _ -> return False
  unless areTypesOk $ throwPosError "Equality operator expected objects of same type, or with common super class"
  when (t1 == TCC.Void) $ throwPosError "Cannot compare void values"
  simplifyExpr $ ERel (RValue TCC.Bool) e1 (insertNoneType opr) e2

_checkExpr (ERel pos op1 opr op2) = binOpCheck op1 op2 (TCC.Int, TCC.Int, TCC.Bool) (\t e1 -> ERel t e1 (insertNoneType opr))

_checkExpr (EAnd pos op1 op2) = binOpCheckTrio op1 op2 TCC.Bool EAnd

_checkExpr (EOr pos op1 op2) = binOpCheckTrio op1 op2 TCC.Bool EOr

_checkExpr (ENull p t) = do
  let nt = mapType t
  case nt of
    TCC.Str -> return  $ ENull (RValue TCC.Str) (insertNoneType t)
    c@TCC.Class{} -> return $ ENull (RValue c) (insertNoneType t)
    c@TCC.Array{} -> return $ ENull (RValue c) (insertNoneType t)
    _ -> throwPosError "Null cannot be cast to primitive type"

type BinOpCreator = TCC.AllocType -> Expr TCC.AllocType -> Expr TCC.AllocType -> Expr TCC.AllocType

insertNoneType::(Functor f) => f a -> f TCC.AllocType
insertNoneType = fmap (const $ RValue None)

binOpCheck::(Positionable a) => Expr a -> Expr a -> (TCC.Type, TCC.Type, TCC.Type) -> BinOpCreator -> TypeChecker (Expr TCC.AllocType)
binOpCheck op1 op2 (t1, t2, r) cr = do
  e1 <- checkExpr op1
  e2 <- checkExpr op2
  expectsTypeAE t1 e1
  expectsTypeAE t2 e2
  simplifyExpr $ cr (RValue r) e1 e2

binOpCheckTrio::(Positionable a) => Expr a -> Expr a -> TCC.Type -> BinOpCreator -> TypeChecker (Expr TCC.AllocType)
binOpCheckTrio op1 op2 t = binOpCheck op1 op2 (t,t,t)

