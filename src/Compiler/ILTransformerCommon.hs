{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
module Compiler.ILTransformerCommon(
  module Compiler.ILTransformerCommon,
  module Control.Monad.State
) where

import Llvm
import AbsLatte as A
import TypeChecker.TypeCheckUtils as TCU
import Control.Monad.State
import qualified Data.Map as M
import FastString (mkFastString)
import Control.Lens
import Control.Monad.Writer
import Data.Maybe

mkfs = mkFastString

mapTypes::TCU.Type -> LlvmType
mapTypes TCU.Int = i32
mapTypes TCU.Bool = i1
mapTypes TCU.Void = LMVoid
mapTypes TCU.Str = i8Ptr
mapTypes (TCU.Array t) = LMStructU [i32, LMPointer $ valType $ mapTypeBack t]
mapTypes (TCU.Class name) = LMAlias (mkFastString name, LMVoid)

valTType::TCU.Type -> LlvmType
valTType = valType . mapTypeBack

valType::A.Type a -> LlvmType
valType t@A.Class{} = LMPointer $ map2Type t
valType t@A.Array{} = LMPointer $ map2Type t
valType t = map2Type t

map2Type::A.Type a -> LlvmType
map2Type = mapTypes . TCU.mapType

type Translator = State (M.Map String LlvmVar, Int)

type StmtWriter = WriterT [LlvmStatement] (LocalT (M.Map String (LlvmVar, Bool)) Translator)

addStmt::LlvmStatement -> StmtWriter ()
addStmt = tell . ( :[])

sAddVar:: String -> LlvmVar -> StmtWriter ()
sAddVar n v = lift $ lift $ addVar n v

sAssign::LlvmType -> LlvmExpression -> StmtWriter LlvmVar
sAssign t e = do
  nVar <- lift $ lift $ newVar t
  addStmt $ Assignment nVar e
  return nVar

addVar::String -> LlvmVar -> Translator ()
addVar n v = modify (over _1 (M.insert n v))

getVar::String -> Translator LlvmVar
getVar n = gets ((M.! n) . fst)

sGetVar::String -> StmtWriter LlvmVar
sGetVar = lift . lift . getVar

sAddLocalVar::String -> LlvmVar -> Bool -> StmtWriter ()
sAddLocalVar n v b = modLocal (M.insert n (v, b))

hasLocalVar::String -> StmtWriter Bool
hasLocalVar n = isJust . (M.!? n) <$> getLocal

getLocalVar::String -> StmtWriter LlvmVar
getLocalVar n = fst . (M.! n) <$> getLocal

createConstString::String -> Translator LlvmVar
createConstString s = do
  let ns = "#str_" ++ s
  v <- gets ((M.!? ns) . fst)
  case v of
    Just v -> return v
    Nothing -> do
                  c <- gets snd
                  modify (over _2 ( + 1))
                  let nVar = LMGlobalVar (mkfs $ "_cstr_" ++ show c) (LMArray (length s +1) i8) Private Nothing Nothing Constant
                  addVar ns nVar
                  return nVar


newVar::LlvmType -> Translator LlvmVar
newVar t = do
  c <- gets snd
  modify (over _2 ( + 1))
  return $ LMNLocalVar (mkfs $ "var" ++  show c) t

sNewVar::LlvmType -> StmtWriter LlvmVar
sNewVar = lift . lift . newVar

malloc::LlvmVar
malloc = LMGlobalVar (mkfs "malloc") (LMFunction LlvmFunctionDecl{
  decName = mkfs "malloc",
  funcLinkage = External,
  funcCc = CC_Fastcc,
  decReturnType = i8Ptr,
  decVarargs = FixedArgs,
  decParams = [(i64,[])],
  funcAlign = Nothing
}) Internal Nothing Nothing Constant


memset::LlvmVar
memset = LMGlobalVar (mkfs "llvm.memset.p0i8.i64") (LMFunction LlvmFunctionDecl{
  decName = mkfs "llvm.memset.p0i8.i64",
  funcLinkage = External,
  funcCc = CC_Fastcc,
  decReturnType = Llvm.LMVoid,
  decVarargs = FixedArgs,
  decParams = [(i8Ptr,[]),(i8,[]),(i64,[]),(i32,[]),(i1,[])],
  funcAlign = Nothing
}) Internal Nothing Nothing Constant

litNum::Integer -> LlvmType -> LlvmVar
litNum v t = LMLitVar (LMIntLit v t)

callMemset::LlvmVar -> LlvmVar -> LlvmStatement
callMemset ptr size = Llvm.Expr (Call StdCall memset [ptr, litNum 0 i8, size, litNum 1 i32, litNum 0 i1] [])

newtype LocalT s m a = LocalT {runLocal:: s -> m (a, s)}

instance (Monad m) => Functor (LocalT s m) where
  fmap f m = m >>= (return . f)

instance (Monad m) => Applicative (LocalT s m) where
  pure = return
  f <*> a = do nf <- f
               nf <$> a

instance (Monad m) => Monad (LocalT a m) where
  return a = LocalT{ runLocal = \s -> return (a,s)}
  f >>= m = LocalT { runLocal = \s -> runLocal f s >>= (\(a,ns) -> runLocal (m a) ns)}

instance MonadTrans (LocalT a) where
  lift m = LocalT {runLocal = \s -> (,s) <$> m}


evalLocal::(Monad m) => LocalT s m a -> s -> m s
evalLocal l s = snd <$> runLocal l s

class MonadLocal s m | m -> s where
   getLocal::(Monad m) => m s
   modLocal::(Monad m) => (s -> s) -> m ()

instance (Monad m) => MonadLocal s (LocalT s m) where
  getLocal = LocalT {runLocal = \s -> return (s,s)}
  modLocal f = LocalT {runLocal = \s -> return ((), f s)}

instance (Monoid a, Monad m, MonadLocal s m) => MonadLocal s (WriterT a m) where
  getLocal = lift getLocal
  modLocal = lift . modLocal


instance (MonadState s m) => MonadState s (LocalT l m)  where
  get = lift get
  put = lift . put
  state = lift . state


replaceVars::LlvmVar -> LlvmVar -> LlvmBlock -> LlvmBlock
replaceVars from to b = b {blockStmts = map (replaceVarsInStmt from to) $ blockStmts b}

replaceVarsInStmt::LlvmVar -> LlvmVar -> LlvmStatement -> LlvmStatement
replaceVarsInStmt f t (Assignment d e) = Assignment (rviv f t d) (replaceVarsInExpr f t e)
replaceVarsInStmt f t (Branch b) = Branch (rviv f t b)
replaceVarsInStmt f t (BranchIf b ift iff) = BranchIf (rviv f t b) (rviv f t ift) (rviv f t iff)
replaceVarsInStmt f t (Expr a) = Expr (replaceVarsInExpr f t a)
replaceVarsInStmt f t (Return v) = Return $ fmap (replaceVarInVar f t) v

replaceVarInVar::LlvmVar -> LlvmVar -> LlvmVar -> LlvmVar
replaceVarInVar from to var | from == var = to
replaceVarInVar _ _ var = var

rviv = replaceVarInVar

replaceVarsInExpr::LlvmVar -> LlvmVar -> LlvmExpression -> LlvmExpression
replaceVarsInExpr from to a@Alloca{} = a
replaceVarsInExpr f t (LlvmOp op a b) = LlvmOp op (rviv f t a) (rviv f t b)
replaceVarsInExpr f t (Compare op a b) = Compare op (rviv f t a) (rviv f t b)
replaceVarsInExpr f t (Load a) = Load (rviv f t a)
replaceVarsInExpr f t (GetElemPtr b v args) = GetElemPtr b (rviv f t v) (map (rviv f t) args)
replaceVarsInExpr f t (Cast op v typ) = Cast op (rviv f t v) typ
replaceVarsInExpr f t (Call typ on args w) = Call typ (rviv f t on) (map (rviv f t ) args ) w
replaceVarsInExpr f t (Phi typ p) = Phi typ $ map (\(a,b) -> (rviv f t a, rviv f t b))  p