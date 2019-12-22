{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}

module TypeChecker.TypeCheckCommon where

import Data.Maybe
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans
import Control.Monad.Except
import qualified Data.Map as M
import Control.Monad
import GHC.Base((<|>), Alternative)
import Control.Lens
import Data.List.Lens
import TypeChecker.TypeCheckUtils
import TypeChecker.TypeUtils


import qualified AbsLatte as A
import Common.ASTUtils (extract)

$(makeLenses ''Env)

concatStrFunc = "__concatStrings"
cmpStrFunc = "__cmpStrings"

baseStack::StackEnv
baseStack = [
  Env {
    _functions = M.fromList [
                      ("printInt", FunctionInfo "printInt" Void [Int]),
                      ("printString", FunctionInfo "printString" Void [Str]),
                      ("error", FunctionInfo "error" Void []),
                      ("readInt", FunctionInfo "readInt" Int []),
                      ("readString", FunctionInfo "readString" Str []),
                      (concatStrFunc, FunctionInfo concatStrFunc Str [Str, Str]),
                      (cmpStrFunc, FunctionInfo cmpStrFunc Bool [Str, Str])
                  ],
    _classInfos = M.empty,
    _variables = M.empty,
    _variableMapping = M.empty
    }
  ]

classI ::String -> Lens' Env (Maybe ClassInfo)
classI a = classInfos . at a

varL :: String -> Lens' Env (Maybe Variable)
varL a = variables . at a

functionI :: String -> Lens' Env (Maybe FunctionInfo)
functionI a = functions . at a

varMappingL :: String -> Lens' Env (Maybe String)
varMappingL a = variableMapping . at a

current::Lens' [a] a
current = lens head (flip (:) . tail)


withVariable::String -> Type ->StackEnv -> StackEnv
withVariable name typ = (current . varL name) ?~ LocalVar name typ

mapVariable::String -> Integer -> StackEnv -> StackEnv
mapVariable name counter = (current . varMappingL name) ?~ ("__v_" ++ show counter)

declareLocalVariable::(MonadReader StackEnv m, MonadState Integer m) => String -> Type -> m (String, StackEnv -> StackEnv)
declareLocalVariable name typ = do
                              currentC <- get
                              modify (+ 1)
                              let envModifier = mapVariable name currentC . withVariable name typ
                              return ("__v_" ++ show currentC, envModifier)

newIdentifier::(MonadState Integer m) => m String
newIdentifier = do
                currentC <- get
                modify (+ 1)
                return $ "__v_" ++ show currentC


withFunction::String -> FunctionInfo -> StackEnv ->StackEnv
withFunction name fInfo = (current . functionI name) ?~ fInfo

withClass::String -> ClassInfo -> StackEnv -> StackEnv
withClass name cInfo = (current . classI name) ?~ cInfo

markAsOverriden::String -> String -> StackEnv -> StackEnv
markAsOverriden method cName s = 
  let ci = fromJust $ s ^. (current . classI cName) in
  let nc = asOverriden method ci in
  let ns = withClass cName nc s in
  case _baseClass nc of
    Nothing -> ns
    Just b -> markAsOverriden method b ns

getInScope::(MonadReader StackEnv m) =>Scope -> Lens' Env (Maybe a) -> m (Maybe a)
getInScope Local l = view $ current . l
getInScope Global l = findInStackEnv (view l)

existsInScope::(MonadReader StackEnv m) =>Scope -> Lens' Env (Maybe a) -> m Bool
existsInScope scope l = isJust <$> getInScope scope l

existsClass::(MonadReader StackEnv m) => String -> Scope -> m Bool
existsClass name s = s `existsInScope` classI name

existsVariable::(MonadReader StackEnv m) =>String -> Scope -> m Bool
existsVariable name s = s `existsInScope` varL name

existsFunction::(MonadReader StackEnv m) => String -> Scope -> m Bool
existsFunction name s = s `existsInScope` functionI name

retVarName::String
retVarName = "__return"

thisName::String
thisName = "__this"

inErrorContext::(MonadRErrorC String m, Show ctx) => ctx -> m a -> m a
inErrorContext ectx tc = mCatchError tc (\e -> mThrowError $ "Error in " ++ show ectx ++ " context: \n" ++ e)

toFuncDef::A.TopDef a -> FunctionInfo
toFuncDef (A.FnDef _ rType (A.Ident name) args _) =
  FunctionInfo name (mapType rType) $ map mapType [t | A.Arg _ t _ <- args]

typeExists::Type -> TypeChecker ()
typeExists t = isTypeDefined t >>= (\b -> unless b $ throwPosError $ "Type " ++ show t ++ "is not defined")

wrongArgsNumber::Int -> Int -> TypeChecker b
wrongArgsNumber exp got = throwPosError $ "Wrong number of arguments. Expected: " ++ show exp ++ " got: " ++ show got
