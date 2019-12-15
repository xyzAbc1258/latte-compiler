module TypeChecker.TypeCheckerStmts where

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
import TypeChecker.TypeCheckerExpr

checkBlock::(Positionable a) => Block a -> TypeChecker (Block TCC.Type)
checkBlock (Block _ stmts) = Block TCC.None <$> local (emptyEnv :) (checkStmts stmts)

checkStmts::(Positionable a) => [Stmt a] -> TypeChecker [Stmt TCC.Type]
checkStmts [] = return []

checkStmts (Empty _ : t) = checkStmts t

--checkStmts (BStmt _ (Block _ [s@BStmt{}]) : t) = checkStmts (s:t)
checkStmts (BStmt _ b@Block{} : t) = (:) <$> (BStmt TCC.None <$> checkBlock b) <*> checkStmts t

checkStmts (Decl pos typ items : t) = do
  let nt = mapType typ
  when (nt == TCC.Void) $ mPosThrowError pos "Cannot declare variable of type void"
  let varNames = [n | Init _ (Ident n) _ <- items] ++ [n | NoInit _ (Ident n) <- items]
  let initExprs = fmap (() <$) [e | Init _ _ e <- items] ++ [defaultValue nt | NoInit{} <- items]
  unless (unique varNames) $ mPosThrowError pos "Variable names has to be unique"
  alreadyDeclared <- filterM (`existsVariable` Local) varNames
  unless (null alreadyDeclared) $ mPosThrowError pos $ "Variables " ++ show alreadyDeclared ++ " were already declared"
  exprs <- mapM checkExpr initExprs
  mapM_ (expectsTypeAE nt) exprs
  (mappedNames, modifiers) <- unzip <$> mapM (`declareLocalVariable` nt) varNames
  let declareNew = foldl1 (.) modifiers
  let newDecl = Decl nt (None <$ typ) (zipWith (Init nt . Ident) mappedNames (map (fmap getType) exprs))
  (newDecl :) <$> local declareNew (checkStmts t)

checkStmts (Ass pos lhs rhs : t) = do
  lhsType <- checkExpr lhs
  rhsType <- checkExpr rhs
  case extract lhsType of
    RValue _ -> mPosThrowError pos "Left side of assignment has to be a lvalue!!"
    LValue t -> expectsTypeAE t rhsType
  (Ass None (fmap getType lhsType) (fmap getType rhsType) :) <$> checkStmts t

checkStmts (Incr v expr : t) =
  checkStmts $ Ass v expr (EAdd v expr (Plus v) (ELitInt v 1)): t

checkStmts (Decr v expr : t) =
  checkStmts $ Ass v expr (EAdd v expr (Minus v) (ELitInt v 1)): t

checkStmts (Ret _ expr : t) = do
  var <- fromJust <$> getInScope Global (varL retVarName)
  let retType = varType var
  exprType <- checkExpr expr
  expectsTypeAE retType exprType
  checkStmts t
  return [Ret retType (fmap getType exprType)]

checkStmts (VRet pos : t) = do
  var <- fromJust <$> getInScope Global (varL retVarName)
  let retType = varType var
  unless (retType == TCC.Void) $ mPosThrowError pos "Wrong return type"
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
  (nName, varMap) <- declareLocalVariable v nt
  bodyExpr <- case body of
    BStmt _ (Block _ l) -> (: []) . BStmt None . Block None <$> local (varMap . (emptyEnv :)) (checkStmts l)
    l -> local (varMap . (emptyEnv :)) $ checkStmts [l]
  let [sb] = bodyExpr
  iteratorIdent <- newIdentifier
  let decl = Decl None (AbsLatte.Int None) [Init None (Ident iteratorIdent) (ELitInt TCC.Int 0)]
  let iteratorVar = EVar TCC.Int (Ident iteratorIdent)
  let elemDecl = Decl None (None <$ typ) [Init None (Ident nName) (EArrAcc nt collExpr iteratorVar)]
  let incrementIter = Ass None iteratorVar (EAdd TCC.Int iteratorVar (Plus None) (ELitInt TCC.Int 1))
  let newSb = case sb of
                BStmt _ (Block _ l) -> BStmt None (Block None (elemDecl : l ++ [incrementIter]))
                s -> BStmt None (Block None (elemDecl : s : [incrementIter]))
  let condition = ERel TCC.Bool iteratorVar (LTH None) $ EFldNoAcc nt collExpr 0
  let while = While None condition newSb
  (\l -> decl : while : l) <$> checkStmts t

checkStmts (SExp _ expr : t) = do
  ex <- checkExpr expr
  (SExp None (fmap getType ex) :) <$> checkStmts t

