{-# LANGUAGE FlexibleContexts #-}
module TypeChecker.TypeUtils(
  module TypeChecker.TypeUtils,
  (<|>)
) where

import TypeChecker.TypeCheckUtils
import Control.Monad.Reader
import qualified Data.Map as M
import qualified AbsLatte as A
import Common.ASTUtils
import Control.Monad
import Control.Monad.Reader
import Data.Maybe
import Control.Applicative((<|>))


primitives = [Int, Str, Bool, Void]

isPrimitive::Type -> Bool
isPrimitive x = x `elem` primitives

getType::AllocType -> Type
getType (LValue t) = t
getType (RValue t) = t

sameAlloc::AllocType -> AllocType -> Bool
sameAlloc (LValue _) (LValue _) = True
sameAlloc (RValue _) (RValue _) = True
sameAlloc _ _ = False


inheritanceList::(MonadReader StackEnv m) => String -> m [String]
inheritanceList s = do
  ci <- fromJust <$> findInStackEnv ((M.!? s) . _classInfos)
  rest <- fromJust (fmap inheritanceList (_baseClass ci) <|> Just (return []))
  return $ _name ci : rest


{-a << b-}
isAssignableClass::(MonadReader StackEnv m) => String -> String -> m Bool
isAssignableClass a b = elem b <$> inheritanceList a

{-x is y-}
isConvertible::(MonadReader StackEnv m) =>Type -> Type -> m Bool
isConvertible x y | x == y = return True
isConvertible (Class a) (Class b) = isAssignableClass a b
isConvertible (Fun r1 a1) (Fun r2 a2) = do
  retConv <- isConvertible r1 r2
  argsConv <- zipWithM isConvertible a2 a1
  return $ length a1 == length a2 && and argsConv && retConv
isConvertible _ _ = return False

isTypeDefined::(MonadReader StackEnv m) => Type -> m Bool
isTypeDefined x | isPrimitive x = return True
isTypeDefined (Class name) = asks (any (M.member name . _classInfos))
isTypeDefined (Array t) = isTypeDefined t

-- Expectations --

expectsType::(MonadRErrorC String m, MonadReader StackEnv m) => Type -> Type -> m ()
expectsType exp got = isConvertible got exp >>= (\ b -> unless b $ mThrowError $ "Expected " ++ show exp ++ " got " ++ show got)

expectsAllocType::(MonadRErrorC String m, MonadReader StackEnv m) => AllocType -> AllocType -> m ()
expectsAllocType exp got = do
  b <-isConvertible (getType got) (getType exp)
  unless (sameAlloc exp got && b) $ mThrowError $ "Expected " ++ show exp ++ " got " ++ show got

expectsTypeA::(MonadRErrorC String m, MonadReader StackEnv m) =>Type -> AllocType -> m()
expectsTypeA t a = expectsType t (getType a)

expectsTypeAE::(MonadRErrorC String m, MonadReader StackEnv m) =>Type -> A.Expr AllocType -> m()
expectsTypeAE t e = expectsTypeA t $ extract e
