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

addVar::String -> LlvmVar -> Translator ()
addVar n v = modify (over _1 (M.insert n v))

getVar::String -> Translator LlvmVar
getVar n = gets ((M.! n) . fst)

newVar::LlvmType -> Translator LlvmVar
newVar t = do
  c <- gets snd
  modify (over _2 ( + 1))
  return $ LMNLocalVar (mkfs $ "var" ++  show c) t


