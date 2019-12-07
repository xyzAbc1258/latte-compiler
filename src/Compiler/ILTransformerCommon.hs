module Compiler.ILTransformerCommon(
  module Compiler.ILTransformerCommon,
  module Control.Monad.State
) where

import Llvm
import AbsLatte as A
import TypeChecker.TypeCheckUtils as TCU
import Control.Monad.State
import Data.Map as M
import FastString (mkFastString)
import Control.Lens
import Control.Monad.Writer

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

type StmtWriter = WriterT [LlvmStatement] Translator

addStmt::LlvmStatement -> StmtWriter ()
addStmt = tell . ( :[])

sAddVar:: String -> LlvmVar -> StmtWriter ()
sAddVar n v = lift $ addVar n v

sAssign::LlvmType -> LlvmExpression -> StmtWriter LlvmVar
sAssign t e = do
  nVar <- lift $ newVar t
  addStmt $ Assignment nVar e
  return nVar

addVar::String -> LlvmVar -> Translator ()
addVar n v = modify (over _1 (M.insert n v))

getVar::String -> Translator LlvmVar
getVar n = gets ((M.! n) . fst)

sGetVar::String -> StmtWriter LlvmVar
sGetVar = lift . getVar

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
sNewVar = lift . newVar

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