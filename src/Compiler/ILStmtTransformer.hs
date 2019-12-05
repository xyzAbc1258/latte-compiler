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
  (stmts, values) <- mapAndUnzipM transformRExpr [e | Init _ _ e <- inits]
  let stores = zipWith Store values varNames
  zipWithM_ addVar names varNames
  return $ declarations ++ (stmts >>= id) ++ stores

transformStmt (Ass _ lhs rhs) = do
  (s1, ptr) <- transformLExpr lhs
  (s2, v) <- transformRExpr rhs
  return $ s1 ++ s2 ++ [Store v ptr]

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

transformStmt (Jump _ (Ident label)) = return [Branch $ LMNLocalVar (mkfs label) LMLabel ]

transformStmt (CondJump _ cond (Ident ifTLabel) (Ident ifFLabel)) = do
  (s1, v) <- transformRExpr cond
  let trueL = LMNLocalVar (mkfs ifTLabel) LMLabel
  let falseL = LMNLocalVar (mkfs ifFLabel) LMLabel
  return $ s1 ++ [BranchIf v trueL falseL]

transformStmt (SExp _ e) = fst <$> transformRExpr e

transformStmt _ = return []



