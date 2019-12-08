module Compiler.ILStmtTransformer where

import AbsLatte as A
import Compiler.ILTransformerCommon
import TypeChecker.TypeCheckUtils as TCU
import Llvm
import Compiler.ILExprTransformer
import Control.Monad.State

transformStmt::Stmt TCU.Type -> StmtWriter ()
transformStmt (Decl _ t inits) = do
  let names = [n | Init _ (Ident n) _ <- inits]
  let llvmType = valType t
  let varNames = map ((`LMNLocalVar` LMPointer llvmType) . mkfs) names
  zipWithM_ sAddVar names varNames
  let declarations = map (`Assignment` Alloca llvmType 1) varNames
  mapM_ addStmt declarations
  let assigns = [Ass None (EVar (mapType t) n) e | Init _ n e <- inits]
  mapM_ transformStmt assigns

transformStmt (Ass _ (EVar t (Ident name)) rhs) = do
  v <- transformRExpr rhs
  case (valTType t, getVarType v) of
    (t1, t2) | t1 == t2 -> sAddLocalVar name v True
    (t1, t2) -> do
                  cVar <- sAssign t1 (Cast LM_Bitcast v t1)
                  sAddLocalVar name cVar True

transformStmt (Ass _ lhs rhs) = do
  ptr <- transformLExpr lhs
  v <- transformRExpr rhs
  case (getVarType ptr, getVarType v) of
    (LMPointer t1, t2) | t1 == t2 -> addStmt $ Store v ptr
    (LMPointer i, _) -> do
                          cVar <- sAssign i (Cast LM_Bitcast v i)
                          addStmt $ Store cVar ptr

transformStmt (Incr _ e) = do
  ptr <- transformLExpr e
  v   <- sAssign i32 (Load ptr)
  inc <- sAssign i32 (LlvmOp LM_MO_Add v (number 1))
  addStmt $ Store inc ptr

transformStmt (Decr _ e) = do
  ptr <- transformLExpr e
  v   <- sAssign i32 (Load ptr)
  inc <- sAssign i32 (LlvmOp LM_MO_Add v (number (-1)))
  addStmt $ Store inc ptr

transformStmt (Ret t e) = do
  v <- transformRExpr e
  addStmt $ Return $ Just v

transformStmt VRet{} = addStmt $ Return Nothing

transformStmt (Jump _ (Ident label)) = sGetVar label >>= (addStmt . Branch)

transformStmt (CondJump _ cond (Ident ifTLabel) (Ident ifFLabel)) = do
  v <- transformRExpr cond
  trueL <- sGetVar ifTLabel
  falseL <- sGetVar ifFLabel
  addStmt $ BranchIf v trueL falseL

transformStmt (SExp _ e) = void $ transformRExpr e

transformStmt _ = return ()



