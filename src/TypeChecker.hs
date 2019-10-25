module TypeChecker where

import AbsLatte
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except
import TypeCheckCommon as TCC
import Data.Maybe
import Data.List

checkTypes::Program a -> Either String ()
checkTypes p = runExcept $ runReaderT (checkProgram p) baseStack

checkProgram::Program a -> TypeChecker ()
checkProgram (Program _ defs) = do
    let classes = [c | c@ClDef{} <- defs]
    let funcs = [f | f@FnDef{} <- defs]
    afterClassDecl <- foldl (\a b -> a >>=(\s -> local (const s) b)) ask $ map declare classes
    afterFuncDecl <- foldl (\a b -> a >>=(\s -> local (const s) b)) (return afterClassDecl) $ map declare funcs
    local (const afterFuncDecl) $ checkTopDef defs

declare::TopDef a -> TypeChecker StackEnv
declare f@(FnDef _ rType (Ident name) args _) = do
  exists <- existsFunction name Global
  when exists $ throwError $ "Function " ++ name ++ " was already defined"
  let argTypes = [t | Arg _ t _ <- args]
  let allTypes = map mapType (rType : argTypes)
  inErrorContext name $ mapM_ typeExists allTypes
  let funcInfo = toFuncDef f
  asks (withFunction name funcInfo)

declare (ClDef _ (Ident name) _ _) = do
  exists <- existsClass name Global
  let sameNameAsPrim = name `elem`  (map show primitives)
  when (exists || sameNameAsPrim) $ throwError $ "Type " ++ name ++ " was already declared."
  asks (withClass name $ createClassInfo name)

checkTopDef::[TopDef a] -> TypeChecker ()
checkTopDef (f@(FnDef _ rType (Ident name) args block): rest) = do
  inErrorContext name $ checkFnDef f
  checkTopDef rest


checkTopDef (ClDef _ (Ident name) exts decls : rest) = return ()

checkTopDef [] = do
  mainF <- getInScope Global $ functionI "main"
  when (isNothing mainF) $ throwError "Function main is not defined"
  let (FunctionInfo _ rType args) = fromJust mainF
  unless (rType == TCC.Int) $ throwError "Main has to return void"
  unless (null args) $ throwError "Main cannot have any arguments"

checkFnDef::TopDef a -> TypeChecker()
checkFnDef (FnDef _ rType (Ident name) args block@(Block _ stmts)) = do
  let argTypes = [t | Arg _ t _ <- args]
  let allTypes = map mapType (rType : argTypes)
  let varNames = retVarName : [n | Arg _ _ (Ident n) <- args]
  when (length (nub varNames) /= length varNames) $ throwError "Argument names are not unique"
  let variablesModifier = foldl1 (.) $ zipWith withVariable varNames allTypes
  local variablesModifier $ checkBlock block
  unless (checkHasReturn stmts) $ throwError "There is a branch without return statement"

checkHasReturn::[Stmt a] -> Bool
checkHasReturn [] = False
checkHasReturn (BStmt _ (Block _ b): r) = checkHasReturn (b ++ r)
checkHasReturn (Ret{}:_) = True
checkHasReturn (VRet{} : _) = True
checkHasReturn [Cond _ _ s] = False
checkHasReturn [CondElse _ _ ifT ifF] = checkHasReturn [ifT] && checkHasReturn [ifF]
checkHasReturn [While _ _ b] = checkHasReturn [b]
checkHasReturn [For _ _ _ _ b] = checkHasReturn [b]
checkHasReturn (_:r) = checkHasReturn r

typeExists::TCC.Type -> TypeChecker ()
typeExists t = isTypeDefined t >>= (\b -> unless b $ throwError $ "Type " ++ show t ++ "is not defined")

checkBlock::Block a -> TypeChecker ()
checkBlock (Block _ stmts) = local (emptyEnv : ) $ checkStmts stmts

checkStmts::[Stmt a] -> TypeChecker ()
checkStmts [] = return ()

checkStmts ((Empty _):t) = checkStmts t

checkStmts ((BStmt _ (Block _ b)):t) = do
  local (emptyEnv :) $ checkStmts b
  checkStmts t

checkStmts ((Decl _ typ items):t) = do
  let nt = mapType typ
  let varNames = [n | Init _ (Ident n) _ <- items] ++ [n | NoInit _ (Ident n) <- items]
  let initExprs = [e | Init _ _ e <- items]
  alreadyDeclared <- filterM (flip existsVariable Local) varNames
  unless (null alreadyDeclared) $ throwError $ "Variables " ++ show alreadyDeclared ++ " were already declared"
  mapM_ (\e -> checkExpr e >>= (expects nt)) initExprs
  let declareNew = foldl1 (.) $ map (flip withVariable nt) varNames
  local declareNew $ checkStmts t

checkStmts ((Ass _ lhs rhs):t) = do
  lhsType <- checkExpr lhs --TODO check lvalue
  rhsType <- checkExpr rhs
  expects lhsType rhsType
  checkStmts t

checkStmts ((Incr _ expr):t) = do
  checkExpr expr >>= expects TCC.Int
  checkStmts t

checkStmts ((Decr _ expr):t) = do
  checkExpr expr >>= expects TCC.Int
  checkStmts t

checkStmts ((Ret _ expr):t) = do
  retType <- fromJust <$> getInScope Global (varL retVarName)
  exprType <- checkExpr expr
  expects retType exprType

checkStmts ((VRet _):t) = do
  retType <- fromJust <$> getInScope Global (varL retVarName)
  unless (retType == TCC.Void) $ throwError "Wrong return type"
  checkStmts t

checkStmts ((Cond _ cond ifTrue):t) = do
  checkExpr cond >>= (expects TCC.Bool)
  checkStmts $ ifTrue : t

checkStmts ((CondElse _ cond ifTrue ifElse):t) = do
  checkExpr cond >>= (expects TCC.Bool)
  checkStmts $ ifTrue : ifElse : t

checkStmts ((While _ cond block):t) = do
  checkExpr cond >>= (expects TCC.Bool)
  checkStmts $ block : t

checkStmts ((For _ typ (Ident v) collection body):t) = do
  let nt = mapType typ
  typeExists nt
  checkExpr collection >>= (expects $ TCC.Array nt)
  case body of
    BStmt _ (Block _ l) -> local ((withVariable v nt) . (emptyEnv :)) $ checkStmts l
    l -> local ((withVariable v nt) . (emptyEnv :)) $ checkStmts [l]
  checkStmts t

checkStmts ((SExp _ expr):t) = do
  checkExpr expr
  checkStmts t

checkExpr::Expr a -> TypeChecker TCC.Type
checkExpr (EVar _ (Ident x)) = do
  d <- getInScope Global (varL x)
  when (isNothing d) $ throwError $ "Variable " ++ x ++ " is undefined"
  return $ fromJust d

checkExpr (ELitInt _ i) = return TCC.Int
checkExpr (ELitTrue _) = return TCC.Bool
checkExpr (ELitFalse _) = return TCC.Bool

checkExpr (ENewObj _ (AbsLatte.Class _ (Ident a))) = do
  c <- getInScope Global (classI a)
  unless (isJust c) $ throwError $ "Class " ++ a ++ " doesnt exists"
  return $ TCC.Class a

checkExpr (EObjFldAcc _ obj (Ident fldName)) = do
  objType <- checkExpr obj
  case objType of
    TCC.Array _ -> do unless (fldName == "length") $ throwError "Array doesnt have any other field than length"
                      return TCC.Int
    TCC.Class cname -> do cInfo <- fromJust <$> (getInScope Global (classI cname))
                          let fldType = getClassField fldName cInfo
                          unless (isJust fldType) $ throwError $ "Class " ++ cname ++ " doesn't have field " ++ fldName
                          return $ fromJust fldType
    t -> throwError $ "Type " ++ show t ++ " doesnt have any field!!!"

checkExpr (EObjFuncApp _ obj (Ident fName) args) = do
  objType <- checkExpr obj
  case objType of
    TCC.Class cname -> do cInfo <- fromJust <$> (getInScope Global (classI cname))
                          let funcType = getClassFunc fName cInfo
                          unless (isJust funcType) $ throwError $ "Class " ++ cname ++ "doesnt have method " ++ fName
                          let (TCC.Fun rType tArgs) = fromJust funcType
                          unless (length tArgs == length args) $ throwError "Wrong number of arguments"
                          zipWithM_ (\e t -> checkExpr e >>= (expects t)) args tArgs
                          return rType
    _ -> throwError "Cannot call funtion on sth which is not a class"

checkExpr (ENewArr _ aType length) = do
  checkExpr length >>= (expects TCC.Int)
  let mType = mapType aType
  typeExists mType
  return $ TCC.Array mType


checkExpr (EArrAcc _ arr index) = do
  checkExpr index >>= (expects TCC.Int)
  aType <- checkExpr arr
  case aType of
    TCC.Array t -> return t
    _ -> throwError "Expected expression of type array"

checkExpr (EApp _ (Ident fName) args) = do
  fType <- getInScope Global (functionI fName)
  unless (isJust fType) $ throwError $ "Function " ++ fName ++ " is not defined"
  let (TCC.FunctionInfo _ rType tArgs) = fromJust fType
  unless (length tArgs == length args) $ throwError "Wrong number of arguments"
  zipWithM_ (\e t -> checkExpr e >>= expects t) args tArgs
  return rType

checkExpr (EString _ _) = return TCC.Str
checkExpr (Neg _ a) = do
  checkExpr a >>= expects TCC.Int
  return TCC.Int

checkExpr (Not _ a) = do
  checkExpr a >>= (expects TCC.Bool)
  return TCC.Bool

checkExpr (EMul _ op1 _ op2) = do
  checkExpr op1 >>= (expects TCC.Int)
  checkExpr op2 >>= (expects TCC.Int)
  return TCC.Int

checkExpr(EAdd _  op1 (Plus _) op2) = do
  t1 <- checkExpr op1
  t2 <- checkExpr op2
  unless ((t1,t2) `elem` [(TCC.Int, TCC.Int), (TCC.Str, TCC.Str)]) $ throwError "Couldnt deduce operand types"
  return t1

checkExpr (EAdd _ op1 _ op2) = do
  checkExpr op1 >>= (expects TCC.Int)
  checkExpr op2 >>= (expects TCC.Int)
  return TCC.Int

checkExpr (ERel _ op1 (EQU _) op2) = do
  t1 <- checkExpr op1
  t2 <- checkExpr op2
  unless (t1 == t2) $ throwError "Equality operator expected objects of same type" -- w przypadku obiektów porównujemy wskażniki
  return TCC.Bool

checkExpr (ERel _ op1 (NE _) op2) = do
  t1 <- checkExpr op1
  t2 <- checkExpr op2
  unless (t1 == t2) $ throwError "Inequality operator expected objects of same type"
  return TCC.Bool

checkExpr (ERel _ op1 _ op2) = do
  checkExpr op1 >>= (expects TCC.Int)
  checkExpr op2 >>= (expects TCC.Int)
  return TCC.Bool

checkExpr (EAnd _ op1 op2) = do
  checkExpr op1 >>= (expects TCC.Bool)
  checkExpr op2 >>= (expects TCC.Bool)
  return TCC.Bool

checkExpr (EOr _ op1 op2) = do
  checkExpr op1 >>= (expects TCC.Bool)
  checkExpr op2 >>= (expects TCC.Bool)
  return TCC.Bool