{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
module Common.ASTModifier where
import TypeChecker.TypeCheckUtils(TypeChecker)
import Control.Monad.Cont
import Control.Monad.Identity
import AbsLatte

type S m t = t -> m t

class ASTModifiable t r | t -> r where
  modify::(Monad m) => S m t -> S m r

instance ASTModifiable (Program a) (Program a) where
  modify = id

liftList::(Monad m) => (a -> m a) -> ([a] -> m [a])
liftList = mapM

instance ASTModifiable [TopDef a] (Program a) where
  modify f (Program a t) = Program a <$> f t

instance ASTModifiable (TopDef a) (Program a) where
  modify = modify . liftList

instance ASTModifiable [Stmt a] (Program a) where
  modify f = modify nf
    where nf (FnDef a b c d (Block e bs)) = FnDef a b c d . Block e <$> f bs
          nf x = return x

instance ASTModifiable (Stmt a) (Program a) where
  modify = modify . liftList

modifyI::(ASTModifiable t r) => (t -> t) -> (r -> r)
modifyI f = runIdentity . modify (Identity . f)