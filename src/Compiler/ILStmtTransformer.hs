module Compiler.ILStmtTransformer where

import AbsLatte as A
import Compiler.ILTransformerCommon
import TypeChecker.TypeCheckUtils as TCU
import MyLlvm.Llvm
import Compiler.ILExprTransformer
import Control.Monad.State

transformStmt::Stmt TCU.Type -> StmtWriter ()
transformStmt (Decl _ t inits) = do
  let names = [n | Init _ (Ident n) _ <- inits]
  let llvmType = valType t
  let varNames = map ((`LMNLocalVar` LMPointer llvmType) . mkfs) names
  zipWithM_ sAddVar names varNames
  let declarations = map (`Assignment` Alloca llvmType 1) varNames
  --mapM_ addStmt declarations --ssa sprawia że to nie jest potrzebne
  let assigns = [Ass None (EVar (mapType t) n) e | Init _ n e <- inits]
  mapM_ transformStmt assigns

transformStmt (Ass _ (EVar t (Ident name)) rhs@EVar{}) = do
  v <- transformRExpr rhs
  case (valTType t, getVarType v) of
    (t1, t2) | t1 == t2 -> do --TODO better
                             dummyVar <- sAssign t1 (Dummy v) 
                             sAddLocalVar name dummyVar Write
    (t1, t2) -> do
                  cVar <- sAssign t1 (Cast LM_Bitcast v t1)
                  sAddLocalVar name cVar Write


transformStmt (Ass _ (EVar t (Ident name)) rhs) = do
  v <- transformRExpr rhs
  case (valTType t, getVarType v) of
    (t1, t2) | t1 == t2 -> sAddLocalVar name v Write
    (t1, t2) -> do
                  cVar <- sAssign t1 (Cast LM_Bitcast v t1)
                  sAddLocalVar name cVar Write

transformStmt (Ass _ lhs rhs) = do
  ptr <- transformLExpr lhs
  v <- transformRExpr rhs
  case (getVarType ptr, getVarType v) of
    (LMPointer t1, t2) | t1 == t2 -> addStmt $ Store v ptr
    (LMPointer i, _) -> do
                          cVar <- sAssign i (Cast LM_Bitcast v i)
                          addStmt $ Store cVar ptr

transformStmt (Ret t e) = do
  v <- transformRExpr e
  case (valTType t, getVarType v) of
      (t1, t2) | t1 == t2 -> addStmt $ Return $ Just v
      (t1, t2) -> do
                    cVar <- sAssign t1 (Cast LM_Bitcast v t1)
                    addStmt $ Return $ Just cVar
  

transformStmt VRet{} = addStmt $ Return Nothing

transformStmt (Jump _ (Ident label)) = sGetVar label >>= (addStmt . Branch)

transformStmt (CondJump _ cond (Ident ifTLabel) (Ident ifFLabel)) = do
  v <- transformRExpr cond
  trueL <- sGetVar ifTLabel
  falseL <- sGetVar ifFLabel
  addStmt $ case v of
              (LMLitVar (LMIntLit 1 (LMInt 1))) -> Branch trueL
              (LMLitVar (LMIntLit 0 (LMInt 1))) -> Branch falseL
              _ -> BranchIf v trueL falseL

transformStmt (SExp _ e) = void $ transformRExpr e

transformStmt _ = return ()



