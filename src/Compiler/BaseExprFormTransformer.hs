module Compiler.BaseExprFormTransformer where

import AbsLatte as A
import TypeChecker.TypeCheckUtils as TCU
import Control.Monad.Writer
import Control.Monad.State
import qualified Common.ASTModifier as ASTM

type M = WriterT [Stmt TCU.Type] (State Integer)

makeVar::TCU.Type -> M (Expr TCU.Type)
makeVar t = do
  ind <- get
  modify (+ 1)
  let vName = "__gen_" ++ show ind
  return $ EVar t (Ident vName)

catch::M a -> M(a, [Stmt TCU.Type])
catch = lift . runWriterT

addStmt::Stmt TCU.Type -> M ()
addStmt s = tell [s]

toBaseForm::Program TCU.Type -> Program TCU.Type
toBaseForm p = evalState (ASTM.modify mapStmts p) 0

mapStmts::[Stmt TCU.Type] -> State Integer [Stmt TCU.Type]
mapStmts s = execWriterT (mapM_ toBaseStmtForm s)

toBaseStmtForm::Stmt TCU.Type -> M ()
toBaseStmtForm (Decl a t its) = do
  simplVars <- mapM toBaseExpr [e | Init _ _ e <- its]
  let nInits = zipWith (\nv (Init a n _) -> Init a n nv) simplVars its
  addStmt $ Decl a t nInits

toBaseStmtForm (Ass a e1 e2) = do
  s1 <- toBaseExpr e1
  s2 <- toBaseExpr e2
  addStmt $ Ass a s1 s2

toBaseStmtForm (SExp a e) = do
  s <- toBaseExpr e
  addStmt $ SExp a s

toBaseStmtForm (Cond a cond b) = do
  sCond <- toBaseExpr cond
  (_, inner) <- catch $ toBaseStmtForm b
  let nb = case inner of
                  [a] -> a
                  c -> BStmt None (Block None c)
  addStmt $ Cond a sCond nb

toBaseStmtForm (CondElse a cond ift iff) = do
  sCond <- toBaseExpr cond
  (_, innerT) <- catch $ toBaseStmtForm ift
  (_, innerF) <- catch $ toBaseStmtForm iff
  let nT = case innerT of
                  [a] -> a
                  c -> BStmt None (Block None c)
  let nF = case innerF of
                    [a] -> a
                    c -> BStmt None (Block None c)
  addStmt $ CondElse a sCond nT nF


toBaseStmtForm s@(While a cond b) = addStmt s
  --(v, s) <- listen $ toBaseExpr cond
  --let woDecls = join $ map woDecl s
  --(_, sb) <- catch $ toBaseStmtForm b
  --let nb = case sb of
  --            [BStmt t1 (Block t2 c)] -> BStmt t1 (Block t2 (c ++ woDecls))
  --            [a] -> BStmt None (Block None (a:woDecls))
  --            c -> BStmt None (Block None (c ++ woDecls))
  --mapM_ addStmt s
  --addStmt $ While a v nb

toBaseStmtForm (BStmt a (Block b s)) = do
  nst <- BStmt a . Block b . join . snd <$> mapAndUnzipM (catch . toBaseStmtForm) s
  addStmt nst

toBaseStmtForm s@VRet{} = addStmt s

toBaseStmtForm (Ret a e) = do
  ne <- toBaseExpr e
  addStmt $ Ret a ne

toBaseStmtForm e@Decr{} = addStmt e

toBaseStmtForm e@Incr{} = addStmt e

toBaseStmtForm t = error $ "Non exhaustive " ++ show t

toBaseExpr::Expr TCU.Type -> M (Expr TCU.Type)

toBaseExpr e@(EVar a _) = return e

toBaseExpr e@(ELitInt a _) = return e

toBaseExpr e@(ELitTrue a) = return e

toBaseExpr e@(ELitFalse a) = return e

toBaseExpr (EFldAcc t e f) = do
  simpl <- toBaseExpr e
  return $ EFldAcc t simpl f

toBaseExpr (EArrAcc t arr ind) = do
  simplA <- toBaseExpr arr
  simplInd <- toBaseExpr ind
  return $ EArrAcc t simplA simplInd

toBaseExpr (EApp a f args) = do
  simplF <- toBaseExpr f
  simplArgs <- mapM toBaseExpr args
  return $ EApp a simplF simplArgs

toBaseExpr e@(EString a _) = return e

toBaseExpr e@(ENull a s) = return e

toBaseExpr e@(ENewObj a s) = return e

toBaseExpr (ENewArr a t size) =  ENewArr a t <$> toBaseExpr size

toBaseExpr (Neg a e) = Neg a <$> toBaseExpr e

toBaseExpr (Not a e) = Not a <$> toBaseExpr e

toBaseExpr (EMul a e1 op e2) = (\s -> EMul a s op) <$> toBaseExpr e1 <*> toBaseExpr e2

toBaseExpr (EAdd a e1 op e2) = (\s -> EAdd a s op) <$> toBaseExpr e1 <*> toBaseExpr e2
toBaseExpr (ERel a e1 op e2) = (\s -> ERel a s op) <$> toBaseExpr e1 <*> toBaseExpr e2

toBaseExpr (EAnd a e1 e2) = do
  simpl1 <- toBaseExpr e1
  nVar <- makeVar TCU.Bool
  addStmt $ Decl None (A.Bool None) $ [Init None (varName nVar) simpl1]
  (simpl2, s) <- listen $ toBaseExpr e2
  addStmt $ Cond None nVar (BStmt None (Block None (s ++ [Ass None nVar simpl2])))
  return nVar

toBaseExpr (EOr a e1 e2) = do
  simpl1 <- toBaseExpr e1
  nVar <- makeVar TCU.Bool
  addStmt $ Decl None (A.Bool None) [Init None (varName nVar) simpl1]
  (simpl2, s) <- listen $ toBaseExpr e2
  addStmt $ Cond None (Not TCU.Bool nVar) (BStmt None (Block None (s ++ [Ass None nVar simpl2])))
  return nVar

toBaseExpr (EVirtCall a obj ind args) = (\s -> EVirtCall a s ind) <$> toBaseExpr obj <*> mapM toBaseExpr args
toBaseExpr (EFldNoAcc a obj ind) = (\s -> EFldNoAcc a s ind) <$> toBaseExpr obj

varName (EVar _ t) = t

woDecl::Stmt TCU.Type -> [Stmt TCU.Type]
woDecl (Decl a t items) = [Ass None (EVar (mapType t) n) e | Init _ n e <- items]
woDecl t = [t]