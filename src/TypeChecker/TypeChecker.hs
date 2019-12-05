{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}

module TypeChecker.TypeChecker where

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

checkTypes::Program a -> Either String (Program TCC.Type)
checkTypes p = runExcept $ runReaderT (evalStateT (checkProgram p) 0)  baseStack

checkProgram::Program a -> TypeChecker (Program TCC.Type)
checkProgram (Program _ defs) = do
    let classes = [c | c@ClDef{} <- defs]
    let inheritances = map (\(ClDef _ (Ident name) ext _) -> (name, case ext of
                                                                      NoExt{} -> []
                                                                      ClassExt _ (Ident c) -> [c])) classes

    unless (unique $ map fst inheritances) $ mThrowError "Class names must be unique"
    let inheritanceGraph = Gr.fromList inheritances
    when (Gr.hasCycle inheritanceGraph) $ mThrowError "Cycle in classes inheritance"
    let classesMap = M.fromList [(n,c) | c@(ClDef _ (Ident n) _ _) <- classes]
    let orderClasses = map (classesMap M.!) $ fromJust $ Gr.sortTopologically inheritanceGraph
    let funcs = [f | f@FnDef{} <- defs]
    let baseClassDecl = foldl (.) id [withClass n (createClassInfo n) |ClDef _ (Ident n) _ _ <- orderClasses]
    afterClassDecl <- local baseClassDecl $ foldl (\a b -> a >>=(\s -> local (const s) b)) ask $ map declare orderClasses
    afterFuncDecl <- foldl (\a b -> a >>=(\s -> local (const s) b)) (return afterClassDecl) $ map declare funcs
    decls <- local (const afterFuncDecl) $ checkTopDef defs
    --throwError ("e", afterFuncDecl)
    return $ ASTM.modifyI removeBlocks $ Program None decls

declare::TopDef a -> TypeChecker StackEnv
declare f@(FnDef _ rType (Ident name) args _) = do
  exists <- existsFunction name Global
  when exists $ mThrowError $ "Function " ++ name ++ " was already defined"
  let argTypes = [t | Arg _ t _ <- args]
  let allTypes = map mapType (rType : argTypes)
  inErrorContext name $ mapM_ typeExists allTypes
  let funcInfo = toFuncDef f
  asks (withFunction name funcInfo)

declare (ClDef _ (Ident name) ext members) = do
  exists <- existsClass name Global
  let sameNameAsPrim = name `elem` map show primitives
  when sameNameAsPrim $ mThrowError $ "Type " ++ name ++ " was already declared."
  baseClass <- case ext of
    NoExt{} -> return $ createClassInfo name
    ClassExt _ (Ident bClass) -> do
                              existsBaseClass <- existsClass bClass Global
                              unless existsBaseClass $ mThrowError $ "Type " ++ bClass ++ " doesnt exists"
                              bInfo <- fromJust <$> getInScope Global (classI bClass)
                              return $ bInfo {_baseClass = Just bClass, _name = name}
  declareNew <- foldl (>>=) (return baseClass) $ map addDeclaration members
  asks (withClass name declareNew)
  where addDeclaration (ClFld _ t (Ident name)) ci = do
                                                      when (M.member name $ _components ci) $ mThrowError $ "Member " ++ name ++ " was already declared"
                                                      let nt = mapType t
                                                      typeExists nt
                                                      return $ addVariable name nt ci
        addDeclaration (ClFunc _ rType (Ident fName) args _) ci = do
                                                                   let existing = _components ci M.!? fName
                                                                   let resFType = TCC.Fun (mapType rType) (map mapType [t | Arg _ t _ <- args] )
                                                                   when (isJust existing && existing /= Just resFType) $ mThrowError $ "Member " ++ fName ++ " was already declared with different type!"
                                                                   return $ addFunction fName resFType ci

checkTopDef::[TopDef a] -> TypeChecker [TopDef TCC.Type]
checkTopDef (f@(FnDef _ rType (Ident name) args block): rest) = do
  td <- inErrorContext name $ checkFnDef f
  (td ++) <$> checkTopDef rest


checkTopDef (ClDef _ (Ident name) exts decls : rest) = do
  ci <- fromJust <$> getInScope Global (classI name)
  let fNameMap fName = _fMapping (_vtable ci) M.! (_fNameMapping (_vtable ci) M.! fName)
  let fndefs = [FnDef w r (Ident $ fNameMap n) (Arg w (AbsLatte.Class w (Ident name)) (Ident thisName): a) b | (ClFunc w r (Ident n) a b) <- decls]
  let structTypes = _varNameMapping ci & M.toList & map swap & sortOn fst & map snd & map (_components ci M.!) & map mapTypeBack
  let structDef = Struct TCC.None (Ident name) $ map (None <$) structTypes
  let classVTable = _vtable ci
  let fMapping = _fMapping classVTable
  let comps = _components ci
  let funcsDecls = classVTable & _fNameMapping & M.toList & sortOn snd & map (\s -> (fMapping M.! snd s,comps M.! fst s)) & map toFuncDelc
  let vtable = VirtArray None (Ident ("virt_" ++ name)) $ map (None <$) funcsDecls
  r <- local (createEnvFromClassInfo ci :) $ checkTopDef fndefs
  ((structDef : vtable : r) ++) <$> checkTopDef rest
  where toFuncDelc (fname, TCC.Fun ret args) = FuncDecl () (mapTypeBack ret) (Ident fname) (map mapTypeBack (TCC.Class name : args))

checkTopDef [] = do
  mainF <- getInScope Global $ functionI "main"
  when (isNothing mainF) $ mThrowError "Function main is not defined"
  let (FunctionInfo _ rType args) = fromJust mainF
  unless (rType == TCC.Int) $ mThrowError "Main has to return int"
  unless (null args) $ mThrowError "Main cannot have any arguments"
  return []

checkFnDef::TopDef a -> TypeChecker [TopDef TCC.Type]
  --TODO refactor...
checkFnDef (FnDef _ rType (Ident name) args block@(Block _ stmts)) = do
  let argTypes = [t | Arg _ t _ <- args]
  let allTypes = map mapType (rType : argTypes)
  unless (all (/= TCC.Void) (tail allTypes)) $ mThrowError "Function argument cannot have type void"
  let varNames = retVarName : [n | Arg _ _ (Ident n) <- args]
  unless (unique varNames) $ mThrowError "Argument names are not unique"
  nArgs <- mapM (\(Arg a t _) -> Arg a t . Ident <$> newIdentifier) args
  let variablesModifier = foldl1 (.) $ zipWith withVariable varNames allTypes
  let decls = [Decl None (None <$ t) [Init nt id (EVar nt nName)] |((Arg a t id, Arg _ _ nName), nt) <- zip (zip args nArgs) (tail allTypes) ]
  blockE <- local variablesModifier $ checkBlock block
  let (Block n s) = blockE
  let nBlock = Block n (decls ++ s)
  unless (checkHasReturn (head allTypes == TCC.Void) s) $ mThrowError "There is a branch without return statement"
  return [FnDef TCC.None (None <$ rType) (Ident name) (zipWith (<$) (tail allTypes) nArgs) nBlock]

checkHasReturn::Bool -> [Stmt a] -> Bool
checkHasReturn isVoid [] = isVoid
checkHasReturn isVoid (BStmt _ (Block _ b): r) = checkHasReturn isVoid (b ++ r)
checkHasReturn _ (Ret{}:_) = True -- sprawdzanie typów jest gdzieś indziej
checkHasReturn _ (VRet{} : _) = True
checkHasReturn _ [Cond _ _ s] = False
checkHasReturn isVoid (CondElse _ _ ifT ifF :r) = (checkHasReturn isVoid [ifT] && checkHasReturn isVoid [ifF]) || checkHasReturn isVoid r
checkHasReturn isVoid [While _ _ b] = checkHasReturn isVoid [b]
checkHasReturn isVoid [For _ _ _ _ b] = checkHasReturn isVoid [b]
checkHasReturn isVoid (_:r) = checkHasReturn isVoid r

typeExists::TCC.Type -> TypeChecker ()
typeExists t = isTypeDefined t >>= (\b -> unless b $ mThrowError $ "Type " ++ show t ++ "is not defined")

checkBlock::Block a -> TypeChecker (Block TCC.Type)
checkBlock (Block _ stmts) = Block TCC.None <$> local (emptyEnv :) (checkStmts stmts)

checkStmts::[Stmt a] -> TypeChecker [Stmt TCC.Type]
checkStmts [] = return []

checkStmts (Empty _ : t) = checkStmts t

--checkStmts (BStmt _ (Block _ [s@BStmt{}]) : t) = checkStmts (s:t)
checkStmts (BStmt _ b@Block{} : t) = (:) <$> (BStmt TCC.None <$> checkBlock b) <*> checkStmts t

checkStmts (Decl _ typ items : t) = do
  let nt = mapType typ
  when (nt == TCC.Void) $ mThrowError "Cannot declare variable of type void"
  let varNames = [n | Init _ (Ident n) _ <- items] ++ [n | NoInit _ (Ident n) <- items]
  let initExprs = fmap (() <$) [e | Init _ _ e <- items] ++ [defaultValue nt | NoInit{} <- items]
  unless (unique varNames) $ mThrowError "Variable names has to be unique"
  alreadyDeclared <- filterM (`existsVariable` Local) varNames
  unless (null alreadyDeclared) $ mThrowError $ "Variables " ++ show alreadyDeclared ++ " were already declared"
  exprs <- mapM checkExpr initExprs
  mapM_ (expectsTypeAE nt) exprs
  (mappedNames, modifiers) <- unzip <$> mapM (`declareLocalVariable` nt) varNames
  let declareNew = foldl1 (.) modifiers
  let newDecl = Decl nt (None <$ typ) (zipWith (Init nt . Ident) mappedNames (map (fmap getType) exprs))
  (newDecl :) <$> local declareNew (checkStmts t)

checkStmts (Ass _ lhs rhs : t) = do
  lhsType <- checkExpr lhs
  rhsType <- checkExpr rhs
  case extract lhsType of
    RValue _ -> mThrowError "Left side of assignment has to be a lvalue!!"
    LValue t -> expectsTypeAE t rhsType
  (Ass None (fmap getType lhsType) (fmap getType rhsType) :) <$> checkStmts t

checkStmts (Incr _ expr : t) = do
  ex <-checkExpr expr
  expectsAllocType (LValue TCC.Int) (extract ex)
  (Incr TCC.Int (fmap getType ex) :)  <$> checkStmts t --TODO zamienić na x = x+1 ?

checkStmts (Decr _ expr : t) = do
  ex <-checkExpr expr
  expectsAllocType (LValue TCC.Int) (extract ex)
  (Decr TCC.Int (fmap getType ex) :)  <$> checkStmts t

checkStmts (Ret _ expr : t) = do
  var <- fromJust <$> getInScope Global (varL retVarName)
  let retType = varType var
  exprType <- checkExpr expr
  expectsTypeAE retType exprType
  checkStmts t
  return [Ret retType (fmap getType exprType)]

checkStmts (VRet _ : t) = do
  var <- fromJust <$> getInScope Global (varL retVarName)
  let retType = varType var
  unless (retType == TCC.Void) $ mThrowError "Wrong return type"
  checkStmts t
  return [VRet TCC.Void]

checkStmts (Cond _ cond ifTrue : t) = do
  condExpr <- checkExpr cond
  expectsTypeAE TCC.Bool condExpr
  sTrueE <- checkStmts [ifTrue]
  case sTrueE of
     [BStmt _ (Block _ s)] | isSimpleBoolExpr condExpr && fromBoolExpr condExpr -> (s ++) <$> checkStmts t
     [sTrue] | isSimpleBoolExpr condExpr && fromBoolExpr condExpr -> (sTrue :) <$> checkStmts t
     [sTrue] | isSimpleBoolExpr condExpr && not (fromBoolExpr condExpr) -> checkStmts t
     [sTrue] -> (Cond None (fmap getType condExpr) sTrue:) <$> checkStmts t
     _ -> mThrowError  "Error in typing if statement" -- Wewnętrzny błąd nie powinien nigdy wystąpić :)

checkStmts (CondElse _ cond ifTrue ifElse : t) = do
  condExpr <- checkExpr cond
  expectsTypeAE TCC.Bool condExpr
  sTrueE <- checkStmts [ifTrue]
  sFalseE <- checkStmts [ifElse]
  res <- case (sTrueE, sFalseE) of
    (s, _) | isTrueExpr condExpr -> return s
    (_, s) | isFalseExpr condExpr -> return s
    ([sTrue], [sFalse]) -> return [CondElse None (fmap getType condExpr) sTrue sFalse]
    _ -> mThrowError "Error in typing if/else statement" -- Wewnętrzny błąd nie powinien nigdy wystąpić :)
  rstmts <- checkStmts t
  if checkHasReturn False res then return res else return $ res ++ rstmts

checkStmts (While _ cond block : t) = do
  condExpr <- checkExpr cond
  expectsTypeAE TCC.Bool condExpr
  sBlockE <- checkStmts [block]
  rest <- checkStmts t
  case sBlockE of
    [sBlock] | isFalseExpr condExpr -> return rest
    [sBlock] | isTrueExpr condExpr && checkHasReturn False sBlockE -> return sBlockE
    [sBlock] | isTrueExpr condExpr -> return [While None (fmap getType condExpr) sBlock]
    [sBlock] -> return (While None (fmap getType condExpr) sBlock : rest)
    _ -> mThrowError "Internal error"

checkStmts (For _ typ (Ident v) collection body : t) = do
  let nt = mapType typ
  typeExists nt
  collExpr <- fmap getType <$> checkExpr collection
  expectsType (TCC.Array nt) $ extract collExpr
  bodyExpr <- case body of
    BStmt _ (Block _ l) -> (: []) . BStmt None . Block None <$> local (withVariable v nt . (emptyEnv :)) (checkStmts l)
    l -> local (withVariable v nt . (emptyEnv :)) $ checkStmts [l]
  let [sb] = bodyExpr
  iteratorIdent <- newIdentifier
  let decl = Decl None (AbsLatte.Int None) [Init None (Ident iteratorIdent) (ELitInt TCC.Int 0)]
  let iteratorVar = EVar TCC.Int (Ident iteratorIdent)
  let elemDecl = Decl None (None <$ typ) [Init None (Ident v) (EArrAcc nt collExpr iteratorVar)]
  let incrementIter = Incr (None) iteratorVar
  let newSb = case sb of
                BStmt _ (Block _ l) -> BStmt None (Block None (elemDecl : l ++ [incrementIter]))
                s -> BStmt None (Block None (elemDecl : s : [incrementIter]))
  let condition = ERel TCC.Bool iteratorVar (LTH None) $ EFldAcc nt collExpr (Ident "length")
  let while = While None condition newSb
  (\l -> decl : while : l) <$> checkStmts t

checkStmts (SExp _ expr : t) = do
  ex <- checkExpr expr
  (SExp None (fmap getType ex) :) <$> checkStmts t

checkExpr::Expr a -> TypeChecker (Expr TCC.AllocType)
checkExpr (EVar _ (Ident x)) = do
  d <- getInScope Global (varL x)
  when (isNothing d) $ mThrowError $ "Variable " ++ x ++ " is undefined"
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

checkExpr (ELitInt _ i) = return $ ELitInt (RValue TCC.Int) i
checkExpr (ELitTrue _) = return $ ELitTrue (RValue TCC.Bool)
checkExpr (ELitFalse _) = return $ ELitFalse (RValue TCC.Bool)

checkExpr (ENewObj _ (AbsLatte.Class _ (Ident a))) = do
  c <- getInScope Global (classI a)
  unless (isJust c) $ mThrowError $ "Class " ++ a ++ " doesnt exists"
  return $ ENewObj (LValue $ TCC.Class a) (AbsLatte.Class TCC.allocNone (Ident a))

checkExpr (EFldAcc _ obj fld@(Ident fldName)) = do
  objExpr <- checkExpr obj
  case getType (extract objExpr) of
    TCC.Array _ -> do unless (fldName == "length") $ mThrowError "Array doesnt have any other field than length"
                      return $ EFldNoAcc (RValue TCC.Int) objExpr 0
    TCC.Class cname -> do cInfo <- fromJust <$> getInScope Global (classI cname)
                          let fldType = _components cInfo M.!? fldName
                          unless (isJust fldType) $ mThrowError $ "Class " ++ cname ++ " doesn't have member " ++ fldName
                          let fldNo = TCC._varNameMapping cInfo M.! fldName
                          return $ EFldNoAcc (LValue $ fromJust fldType) objExpr fldNo
    t -> mThrowError $ "Type " ++ show t ++ " doesnt have any field!!!"


checkExpr (EApp _ (EVar _ (Ident fName)) args) = do
  fType <- getInScope Global (functionI fName)
  unless (isJust fType) $ mThrowError $ "Function " ++ fName ++ " is not defined"
  let func = fromJust fType
  let (rType, tArgs) = case func of --TODO instance func
                         (TCC.FunctionInfo _ r a) -> (r, a)
                         (TCC.InstanceFunc _ r a) -> (r, a)
  unless (length tArgs == length args) $ mThrowError "Wrong number of arguments"
  argsExpr <- mapM checkExpr args
  zipWithM_ expectsTypeAE tArgs argsExpr
  let retAllocType =case rType of
                      (TCC.Class _) -> RValue
                      (TCC.Array _) -> RValue
                      _ -> LValue
  case func of
    TCC.FunctionInfo{} -> return $ EApp (retAllocType rType) (EVar (RValue (TCC.Fun rType tArgs)) (Ident fName)) argsExpr
    TCC.InstanceFunc{} -> do
                           thisType <- varType . fromJust <$> getInScope Global (varL thisName)
                           let (TCC.Class cName) = thisType
                           cInfo <- fromJust <$> getInScope Global (classI cName)
                           let fNumber = _fNameMapping (_vtable cInfo) M.! fName
                           let thisVar = EVar (LValue thisType) (Ident thisName)
                           return $ EVirtCall (retAllocType rType) thisVar fNumber argsExpr



checkExpr (EApp _ (EFldAcc _ obj (Ident fName)) args) = do
  objExpr <- checkExpr obj
  case getType $ extract objExpr of
    thisType@(TCC.Class cName) -> do --TODO refactor, powtórzenia z funkcją wyżej
                        cInfo <- fromJust <$> getInScope Global (classI cName)
                        let fNumber = _fNameMapping (_vtable cInfo) M.! fName
                        let maybeFType = _components cInfo M.!? fName
                        unless (isJust maybeFType && (isFunc (fromJust maybeFType))) $ mThrowError $ "Class " ++ cName ++ " doesn't have function " ++ fName
                        let (TCC.Fun rType tArgs) = fromJust maybeFType
                        unless (length tArgs == length args) $ mThrowError "Wrong number of arguments"
                        argsExpr <- mapM checkExpr args
                        zipWithM_ expectsTypeAE tArgs argsExpr
                        let retAllocType =case rType of
                                             (TCC.Class _) -> RValue
                                             (TCC.Array _) -> RValue
                                             _ -> LValue
                        return $ EVirtCall (retAllocType rType) objExpr fNumber argsExpr
    _ -> mThrowError "Cannot call function on object which is not a class"

checkExpr (ENewArr _ aType length) = do
  lengthExpr <- checkExpr length
  expectsTypeAE TCC.Int lengthExpr
  let mType = mapType aType
  typeExists mType
  return $ ENewArr (LValue $ TCC.Array mType) (insertNoneType aType) lengthExpr


checkExpr (EArrAcc _ arr index) = do
  eInd <- checkExpr index
  expectsTypeAE TCC.Int eInd
  aExpr <- checkExpr arr
  case getType $ extract aExpr of
    TCC.Array t -> return $ EArrAcc (LValue t) aExpr eInd
    t -> mThrowError $ "Expected expression of type array, got: " ++ show t

checkExpr (EString _ s) = return $ EString (RValue TCC.Str) s

checkExpr (Neg _ a) = do
  inner <- checkExpr a
  expectsTypeAE TCC.Int inner
  simplifyExpr $ Neg (RValue TCC.Int) inner

checkExpr (Not _ a) = do
  inner <- checkExpr a
  expectsTypeAE TCC.Bool inner
  simplifyExpr $ Not (RValue TCC.Bool) inner

checkExpr (EMul _ op1 opr op2) = binOpCheckTrio op1 op2 TCC.Int (\t e1 -> EMul t e1 (insertNoneType opr))

checkExpr(EAdd _  op1 p@(Plus _) op2) = do
  e1 <- checkExpr op1
  e2 <- checkExpr op2
  let t1 = getType $ extract e1
  let t2 = getType $ extract e2
  unless ((t1,t2) `elem` [(TCC.Int, TCC.Int), (TCC.Str, TCC.Str)]) $ mThrowError "Couldnt deduce operand types"
  simplifyExpr $ EAdd (RValue t1) e1 (insertNoneType p) e2

checkExpr (EAdd _ op1 opr@(Minus{}) op2) = binOpCheckTrio op1 op2 TCC.Int (\t e1 -> EAdd t e1 (insertNoneType opr))

checkExpr (ERel _ op1 opr@(EQU _) op2) = do
  e1 <- checkExpr op1
  e2 <- checkExpr op2
  let t1 = getType $ extract e1
  let t2 = getType $ extract e2
  unless (t1 == t2) $ mThrowError "Equality operator expected objects of same type"
  simplifyExpr $ ERel (RValue TCC.Bool) e1 (insertNoneType opr) e2

checkExpr (ERel _ op1 opr@(NE _) op2) = do
  e1 <- checkExpr op1
  e2 <- checkExpr op2
  let t1 = getType $ extract e1
  let t2 = getType $ extract e2
  unless (t1 == t2) $ mThrowError "Inequality operator expected objects of same type"
  simplifyExpr $ ERel (RValue TCC.Bool) e1 (insertNoneType opr) e2

checkExpr (ERel _ op1 opr op2) = binOpCheck op1 op2 (TCC.Int, TCC.Int, TCC.Bool) (\t e1 -> ERel t e1 (insertNoneType opr))

checkExpr (EAnd _ op1 op2) = binOpCheckTrio op1 op2 TCC.Bool EAnd

checkExpr (EOr _ op1 op2) = binOpCheckTrio op1 op2 TCC.Bool EOr

checkExpr (ENull _ t) = do
  let nt = mapType t
  case nt of
    TCC.Str -> return  $ ENull (LValue TCC.Str) (insertNoneType t)
    c@TCC.Class{} -> return $ ENull (LValue c) (insertNoneType t)
    c@TCC.Array{} -> return $ ENull (LValue c) (insertNoneType t)
    _ -> mThrowError "Null cannot be cast to primitive type"

type BinOpCreator = TCC.AllocType -> Expr TCC.AllocType -> Expr TCC.AllocType -> Expr TCC.AllocType

insertNoneType::(Functor f) => f a -> f TCC.AllocType
insertNoneType = fmap (const $ RValue None)

binOpCheck::Expr a -> Expr a -> (TCC.Type, TCC.Type, TCC.Type) -> BinOpCreator -> TypeChecker (Expr TCC.AllocType)
binOpCheck op1 op2 (t1, t2, r) cr = do
  e1 <- checkExpr op1
  e2 <- checkExpr op2
  expectsTypeAE t1 e1
  expectsTypeAE t2 e2
  simplifyExpr $ cr (RValue r) e1 e2

binOpCheckTrio::Expr a -> Expr a -> TCC.Type -> BinOpCreator -> TypeChecker (Expr TCC.AllocType)
binOpCheckTrio op1 op2 t = binOpCheck op1 op2 (t,t,t)

