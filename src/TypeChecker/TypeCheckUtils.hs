{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module TypeChecker.TypeCheckUtils where

import qualified AbsLatte as A
import qualified Data.Map as M
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State
import Control.Lens
import Control.Applicative((<|>), Alternative)
import Common.Utils(E, Defaultable, getDefault)

data Type = Int | Str | Bool | Void | Class String | Fun Type [Type] | Array Type | None deriving(Eq, Show)

instance Defaultable Type where
  getDefault = None

isFunc::Type -> Bool
isFunc (Fun{}) = True
isFunc _ = False

defaultValue::Type -> A.Expr ()
defaultValue Int = A.ELitInt () 0
defaultValue Str = A.EString () ""
defaultValue Bool = A.ELitFalse ()
defaultValue c@Class{} = A.ENull () (mapTypeBack c)
defaultValue a@Array{} = A.ENull () (mapTypeBack a)

mapType:: A.Type a -> Type
mapType (A.Int _) = Int
mapType (A.Str _) = Str
mapType (A.Bool _) = Bool
mapType (A.Void _) = Void
mapType (A.Class _ (A.Ident name)) = Class name
mapType (A.Array _ typ) = Array $ mapType typ
mapType (A.Fun _ rtype args) = Fun (mapType rtype) $ map mapType args

mapTypeBack:: Type -> A.Type ()
mapTypeBack Int = A.Int ()
mapTypeBack Str = A.Str ()
mapTypeBack Bool = A.Bool ()
mapTypeBack Void = A.Void ()
mapTypeBack (Class name) = A.Class () (A.Ident name)
mapTypeBack (Array typ) = A.Array () $ mapTypeBack typ
mapTypeBack (Fun rtype args) = A.Fun () (mapTypeBack rtype) $ map mapTypeBack args


data AllocType = LValue Type |RValue Type deriving (Eq, Show)

allocNone::AllocType
allocNone = LValue None

data FunctionInfo = FunctionInfo String Type [Type] | InstanceFunc String Type [Type] deriving (Show)

data VTable = VTable {
  _fNameMapping :: M.Map String Integer,
  _fMapping :: M.Map Integer String
} deriving (Show)

emptyVTable::VTable
emptyVTable = VTable {_fNameMapping = M.empty, _fMapping = M.empty}

addMapping::String->String-> E VTable
addMapping fName fWithClassName vtable =
  let currentfNameMapping = _fNameMapping vtable
    in let newFNameMapping = M.alter (\ s -> s <|> (Just $ fromIntegral (M.size currentfNameMapping))) fName currentfNameMapping
      in let newFMapping = M.insert (newFNameMapping M.! fName) fWithClassName $ _fMapping vtable
        in VTable {_fNameMapping = newFNameMapping, _fMapping = newFMapping}

data ClassInfo = ClassInfo {
  _name :: String,
  _baseClass :: Maybe String,
  _components :: M.Map String Type,
  _vtable :: VTable,
  _varNameMapping :: M.Map String Integer
} deriving (Show)


createClassInfo::String -> ClassInfo
createClassInfo x = ClassInfo { _name = x, 
                                _baseClass = Nothing, 
                                _components = M.empty, 
                                _vtable = emptyVTable, 
                                _varNameMapping = M.empty
                                }

addVariable::String -> Type -> E ClassInfo
addVariable name vType classInfo = let currComponents = _components classInfo 
                                    in let current = _varNameMapping classInfo
                                     in let new = M.alter (\s -> s <|> (Just $ fromIntegral (M.size current +1))) name current
                                      in classInfo {_varNameMapping = new, _components = M.insert name vType currComponents}

addFunction::String -> Type -> E ClassInfo
addFunction name fType@Fun{} classInfo = let cName = _name classInfo
                                    in let nVTable = addMapping name (cName ++ "_" ++ name) $ _vtable classInfo
                                     in let currComponents = _components classInfo
                                      in classInfo {_vtable = nVTable, _components = M.insert name fType currComponents}


data Variable = LocalVar String Type | Instance String Type deriving (Show)

varType :: Variable -> Type
varType (LocalVar _ t) = t
varType (Instance _ t) = t

data Env = Env {
  _classInfos :: M.Map String ClassInfo,
  _functions :: M.Map String FunctionInfo,
  _variables :: M.Map String Variable,
  _variableMapping :: M.Map String String
} deriving (Show)

emptyEnv::Env
emptyEnv = Env {_classInfos = M.empty, _functions = M.empty, _variables = M.empty, _variableMapping = M.empty}

createEnvFromClassInfo::ClassInfo -> Env
createEnvFromClassInfo ci = M.foldlWithKey (\e k t -> modify k t e) emptyEnv (_components ci)
  where modify f (Fun r args) e = e { _functions = M.insert f (InstanceFunc f r args) $ _functions e}
        modify v t e = e {_variables = M.insert v (Instance v t) $ _variables e}

data Scope = Local | Global

type StackA a = [a]

type StackEnv = StackA Env

type TypeChecker = StateT Integer (ReaderT StackEnv (Except String))

class (Monad m) => MonadRErrorC e m where
  mThrowError::e -> m a
  mCatchError::m a -> (e -> m a) -> m a

instance(Monad m ,MonadError e m) => MonadRErrorC e m where
  mThrowError = throwError
  mCatchError = catchError
  
--instance(Monad m, MonadReader r m, MonadError (e,r) m) => MonadRErrorC e m where
--  mThrowError msg = asks (msg,) >>= throwError
--  mCatchError m f = catchError m (\(e,r) -> catchError (f e) (\(ne,_) -> throwError (ne, r))) --TODO usunąć później


getValue::Alternative f => (a -> f b) -> StackA a -> f b
getValue g [a] = g a
getValue g (h:t) = g h <|> getValue g t

findInStackEnv::(MonadReader StackEnv m) => (Env -> Maybe a) -> m (Maybe a)
findInStackEnv g = asks (getValue g)
