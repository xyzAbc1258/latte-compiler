{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Common.ASTModifier where
import TypeChecker.TypeCheckUtils(TypeChecker)
import Control.Monad.Cont
import AbsLatte

data ASTModifier m a b = ASTModifier {
    modifyProgram::Program a ->m (Program b),
    modifyTopDefs::[TopDef a] -> m [TopDef b],
    modifyTopDef::TopDef a -> m (TopDef b),
    modifyStmts::[Stmt a] -> m [Stmt b],
    modifyStmt::Stmt a -> m (Stmt b),
    modifyExpr::Expr a -> m (Expr b),
    modifyType::Type a -> m (Type b),
    modifyArg::Arg a -> m (Arg b)
}

idModifier::(Monad m) => ASTModifier m a a
idModifier = ASTModifier {
  modifyProgram = return,
  modifyTopDefs = return,
  modifyTopDef = return,
  modifyStmts = return,
  modifyStmt = return,
  modifyExpr = return
}

class ASTModifiable t where
  modify::ASTModifier m a b -> t a -> m (t b)

instance ASTModifiable Program where
  modify = modifyProgram
  
instance ASTModifiable TopDef where
  modify = modifyTopDef
  
instance ASTModifiable Expr where
  modify = modifyExpr
  
instance ASTModifiable Stmt where
  modify = modifyStmt