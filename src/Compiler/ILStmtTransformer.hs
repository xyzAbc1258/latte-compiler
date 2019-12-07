module Compiler.ILStmtTransformer where

import AbsLatte as A
import Compiler.ILTransformerCommon
import TypeChecker.TypeCheckUtils as TCU
import Llvm
import Compiler.ILExprTransformer
import Control.Monad.State

transformStmt::Stmt TCU.Type -> Translator [LlvmStatement]
transformStmt (Decl _ t inits) = do
  let names = [n | Init _ (Ident n) _ <- inits]
  let llvmType = valType t
  let varNames = map ((`LMNLocalVar` LMPointer llvmType) . mkfs) names
  zipWithM_ addVar names varNames
  let declarations = map (`Assignment` Alloca llvmType 1) varNames
  let assigns = [Ass None (EVar (mapType t) n) e | Init _ n e <- inits]
  stores <- join <$> mapM transformStmt assigns
  return $ declarations ++  stores

transformStmt (Ass _ lhs rhs) = do
  (s1, ptr) <- transformLExpr lhs
  (s2, v) <- transformRExpr rhs
  case (getVarType ptr, getVarType v) of
    (LMPointer t1, t2) | t1 == t2 -> return $ s1 ++ s2 ++ [Store v ptr]
    (LMPointer i, _) -> do
                          cVar <- newVar i
                          return $ s1 ++ s2 ++ [Assignment cVar (Cast LM_Bitcast v i), Store cVar ptr]

transformStmt (Incr _ e) = do
  (s1, ptr) <- transformLExpr e
  v <- newVar i32
  inc <- newVar i32
  let stmts = [
                Assignment v (Load ptr),
                Assignment inc (LlvmOp LM_MO_Add v (number 1)),
                Store inc ptr
              ]
  return $ s1 ++ stmts

transformStmt (Decr _ e) = do
  (s1, ptr) <- transformLExpr e
  v <- newVar i32
  inc <- newVar i32
  let stmts = [
                Assignment v (Load ptr),
                Assignment inc (LlvmOp LM_MO_Add v (number (-1))),
                Store inc ptr
              ]
  return $ s1 ++ stmts

transformStmt (Ret t e) = do
  (s1, v) <- transformRExpr e
  return $ s1 ++ [Return $ Just v]

transformStmt VRet{} = return [Return Nothing]

transformStmt (Jump _ (Ident label)) = (: []) . Branch <$> getVar label

transformStmt (CondJump _ cond (Ident ifTLabel) (Ident ifFLabel)) = do
  (s1, v) <- transformRExpr cond
  trueL <- getVar ifTLabel
  falseL <- getVar ifFLabel
  return $ s1 ++ [BranchIf v trueL falseL]

transformStmt (SExp _ e) = fst <$> transformRExpr e

transformStmt _ = return []



