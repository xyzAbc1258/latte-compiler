{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}

module TypeCheckCommon where

import Data.Maybe
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans
import Control.Monad.Except
import qualified Data.Map as M
import Control.Monad
import GHC.Base((<|>), Alternative)
import Data.Maybe(fromJust)
import Control.Lens
import Data.List.Lens

import qualified AbsLatte as A

data Type = Int | Str | Bool | Void | Class String | Fun Type [Type] | Array Type deriving(Eq, Show)

primitives = [Int, Str, Bool, Void]

isPrimitive::Type -> Bool
isPrimitive x = x `elem` primitives



data FunctionInfo = FunctionInfo String Type [Type] | InstanceFunc String Type [Type]

--data FieldInfo = FieldInfo String Type

data ClassInfo = ClassInfo {
  _name :: String,
  _baseClass :: Maybe String,
  _components :: M.Map String Type
}

getClassField::String -> ClassInfo -> Maybe Type
getClassField name ci =
  let mType = _components ci M.!? name in
    case mType of
      Nothing -> Nothing
      (Just t) -> case t of
                    Fun{} -> Nothing
                    t -> Just t

getClassFunc::String -> ClassInfo -> Maybe Type
getClassFunc name ci =
  let mType = _components ci M.!? name in
    case mType of
      Nothing -> Nothing
      (Just t) -> case t of
                    Fun{} -> Just t
                    _ -> Nothing


data Variable = LocalVar String Type | Instance String Type


data Env = Env {
  _classInfos :: M.Map String ClassInfo,
  _functions :: M.Map String FunctionInfo,
  _variables :: M.Map String Type
}

data Scope = Local | Global


$(makeLenses ''Env)

type StackA a = [a]
type StackEnv = StackA Env

baseStack::StackEnv
baseStack = [Env{_functions = M.fromList [
  ("printInt", FunctionInfo "printInt" Void [Int]),
  ("printString", FunctionInfo "printString" Void [Str]),
  ("error", FunctionInfo "error" Void []),
  ("readInt", FunctionInfo "readInt" Int []),
  ("readString", FunctionInfo "readString" Str [])
], _classInfos = M.empty, _variables = M.empty}]

emptyEnv::Env
emptyEnv = Env {_classInfos = M.empty, _functions = M.empty, _variables = M.empty}

$(makeLenses ''ClassInfo)

classI ::String -> Lens' Env (Maybe ClassInfo)
classI a = classInfos . at a

varL :: String -> Lens' Env (Maybe Type)
varL a = variables . at a

functionI :: String -> Lens' Env (Maybe FunctionInfo)
functionI a = functions . at a

current::Lens' [a] a
current = lens head (flip (:))

getValue::Alternative f => (a -> f b) -> StackA a -> f b
getValue g [a] = g a
getValue g (h:t) = g h <|> getValue g t


type TypeChecker = ReaderT StackEnv (Except String)

findInStackEnv:: (Env -> Maybe a) -> TypeChecker (Maybe a)
findInStackEnv g = asks (getValue g)

inheritanceList::String -> TypeChecker [String]
inheritanceList s = do
  ci <- fromJust <$> findInStackEnv ((M.!? s) . _classInfos)
  rest <- fromJust (fmap inheritanceList (_baseClass ci) <|> Just (return []))
  return $ _name ci : rest

{-a << b-}
isAssignableClass::String -> String -> TypeChecker Bool
isAssignableClass a b = elem b <$> inheritanceList a

{-x is y-}
isConvertible::Type -> Type -> TypeChecker Bool
isConvertible x y | x == y = return True
isConvertible (Class a) (Class b) = isAssignableClass a b
isConvertible (Fun r1 a1) (Fun r2 a2) = do
  retConv <- isConvertible r1 r2
  argsConv <- zipWithM isConvertible a2 a1
  return $ length a1 == length a2 && and argsConv && retConv
isConvertible _ _ = return False

withVariable::String -> Type ->StackEnv -> StackEnv
withVariable name typ = (current . varL name) ?~ typ

withFunction::String -> FunctionInfo -> StackEnv ->StackEnv
withFunction name fInfo = (current . functionI name) ?~ fInfo

withClass::String -> ClassInfo -> StackEnv -> StackEnv
withClass name cInfo = (current . classI name) ?~ cInfo

createClassInfo::String -> ClassInfo
createClassInfo x = ClassInfo {_name = x, _baseClass = Nothing, _components = M.empty}

getInScope::Scope -> Lens' Env (Maybe a) -> TypeChecker (Maybe a)
getInScope Local l = asks $ view $ current . l
getInScope Global l = findInStackEnv (view l)

existsInScope::Scope -> Lens' Env (Maybe a) -> TypeChecker Bool
existsInScope scope l = isJust <$> getInScope scope l

existsClass::String -> Scope -> TypeChecker Bool
existsClass name s = s `existsInScope` classI name

existsVariable::String -> Scope -> TypeChecker Bool
existsVariable name s = s `existsInScope` varL name

existsFunction::String -> Scope -> TypeChecker Bool
existsFunction name s = s `existsInScope` functionI name

isTypeDefined::Type -> TypeChecker Bool
isTypeDefined x | isPrimitive x = return True
isTypeDefined (Class name) = existsClass name Global
isTypeDefined (Array t) = isTypeDefined t

retVarName::String
retVarName = "__return"

mapType:: A.Type a -> Type
mapType (A.Int _) = Int
mapType (A.Str _) = Str
mapType (A.Bool _) = Bool
mapType (A.Void _) = Void
mapType (A.Class _ (A.Ident name)) = Class name
mapType (A.Array _ typ) = Array $ mapType typ
mapType (A.Fun _ rtype args) = Fun (mapType rtype) $ map mapType args

inErrorContext::(MonadError String m, Show ctx) => ctx -> m a -> m a
inErrorContext ectx tc = catchError tc (\e -> throwError $ "Error in " ++ show ectx ++ " context: \n" ++ e)

toFuncDef::A.TopDef a -> FunctionInfo
toFuncDef (A.FnDef _ rType (A.Ident name) args _) =
  FunctionInfo name (mapType rType) $ map mapType [t | A.Arg _ t _ <- args]

expects:: Type -> Type -> TypeChecker ()
expects exp got = isConvertible got exp >>= (\ b -> unless b $ throwError $ "Expected " ++ show exp ++ " got " ++ show got)