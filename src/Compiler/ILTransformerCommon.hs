{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
module Compiler.ILTransformerCommon(
  module Compiler.ILTransformerCommon,
  module Control.Monad.State
) where

import MyLlvm.Llvm
import AbsLatte as A
import TypeChecker.TypeCheckUtils as TCU
import Control.Monad.State
import qualified Data.Map as M
import FastString (mkFastString)
import Control.Lens
import Control.Monad.Writer
import Data.Maybe
import MyLlvm.PpLlvm
import Common.Utils
import qualified Data.Set as S
import Data.List

mkfs = mkFastString

mapTypes::TCU.Type -> LlvmType
mapTypes TCU.Int = i32
mapTypes TCU.Bool = i1
mapTypes TCU.Void = LMVoid
mapTypes TCU.Str = i8Ptr
mapTypes (TCU.Array t) = LMStruct [i32, LMPointer $ valType $ mapTypeBack t]
mapTypes (TCU.Class name) = LMAlias (mkfs name, LMVoid)

valTType::TCU.Type -> LlvmType
valTType = valType . mapTypeBack

valType::A.Type a -> LlvmType
valType t@A.Class{} = LMPointer $ map2Type t
--valType t@A.Array{} = LMPointer $ map2Type t
valType t = map2Type t

map2Type::A.Type a -> LlvmType
map2Type = mapTypes . TCU.mapType

type Translator = State (M.Map String LlvmVar, Int)


data VarOps = Read | Write | ReadWrite

varReads::VarOps -> Bool
varReads Write = False
varReads _ = True

varWrites::VarOps -> Bool
varWrites Read = False
varWrites _ = True

type StmtWriter = WriterT [LlvmStatement] (LocalT (M.Map String (LlvmVar, VarOps), [(LlvmVar, LlvmExpression)]) Translator)

addStmt::LlvmStatement -> StmtWriter ()
addStmt = tell . ( :[])

sAddVar:: String -> LlvmVar -> StmtWriter ()
sAddVar n v = lift $ lift $ addVar n v

sAssign::LlvmType -> LlvmExpression -> StmtWriter LlvmVar
sAssign t e = lift (lift $ newVar t) >>= (`tryLocal` e)

forceRememberLocal::LlvmVar -> LlvmExpression -> StmtWriter ()
forceRememberLocal v e = modLocal (_2 %~ (((v, e) :) . filter ((/= e) . snd)))

rememberLocal::LlvmVar -> LlvmExpression -> StmtWriter ()
rememberLocal v e =
  case e of
    Load{} -> return () --loadów dla pewności nie zapisujemy, pewnie czegoś jeszcze też nie
    Alloca{} -> return ()
    e -> modLocal (_2 %~ ((v,e):))

tryLocal::LlvmVar -> LlvmExpression -> StmtWriter LlvmVar
tryLocal nv e = do
  exists <- map fst . filter (( == e) . snd) . snd <$> getLocal
  case exists of
    [v] -> return v
    [] -> do
            addStmt $ Assignment nv e
            rememberLocal nv e
            return nv

addVar::String -> LlvmVar -> Translator ()
addVar n v = modify (_1 %~ M.insert n v)

getVar::String -> Translator LlvmVar
getVar n = gets (getFMap n . fst)

sGetVar::String -> StmtWriter LlvmVar
sGetVar = lift . lift . getVar

sAddLocalVar::String -> LlvmVar -> VarOps -> StmtWriter ()
sAddLocalVar n v b = do
  (l,_) <- getLocal
  let current = snd <$> (l M.!? n)
  case (b, current) of
    (Write, Just Read) -> modLocal (_1 %~ M.insert n (v, ReadWrite))
    (Read, Just Write) -> modLocal (_1 %~ M.insert n (v, Write))
    (_, Just ReadWrite) -> modLocal (_1 %~ M.insert n (v, ReadWrite))
    _ -> modLocal (_1 %~ M.insert n (v, b))

hasLocalVar::String -> StmtWriter Bool
hasLocalVar n = isJust . (M.!? n) . fst <$> getLocal


getFMap::(Show k, Ord k) => k -> M.Map k v -> v
getFMap key m = fromMaybe (error $ "not found: " ++ show key) (m M.!? key)

getFMapI::(Show k, Ord k) => M.Map k v -> k -> v
getFMapI = flip getFMap

getLocalVar::String -> StmtWriter LlvmVar
getLocalVar n = fst . (getFMap n) . fst <$> getLocal

createConstString::String -> Translator LlvmVar
createConstString s = do
  let ns = "#str_" ++ s
  v <- gets ((M.!? ns) . fst)
  case v of
    Just v -> return v
    Nothing -> do
                  c <- gets snd
                  modify (_2 %~ ( + 1))
                  let nVar = LMGlobalVar (mkfs $ "_cstr_" ++ show c) (LMArray (sLength (convertString s) +1) i8) Private Nothing Nothing Constant
                  addVar ns nVar
                  return nVar


newVar::LlvmType -> Translator LlvmVar
newVar t = do
  c <- gets snd
  modify (_2 %~ ( + 1))
  return $ LMNLocalVar (mkfs $ "var" ++  show c) t

sNewVar::LlvmType -> StmtWriter LlvmVar
sNewVar = lift . lift . newVar

malloc::LlvmVar
malloc = LMGlobalVar (mkfs "malloc") (LMFunction LlvmFunctionDecl{
  decName = mkfs "malloc",
  funcLinkage = External,
  funcCc = CC_Ccc,
  decReturnType = i8Ptr,
  decVarargs = FixedArgs,
  decParams = [(i64,[])],
  funcAlign = Nothing
}) Internal Nothing Nothing Constant


memset::LlvmVar
memset = LMGlobalVar (mkfs "llvm.memset.p0i8.i64") (LMFunction LlvmFunctionDecl{
  decName = mkfs "llvm.memset.p0i8.i64",
  funcLinkage = External,
  funcCc = CC_Ccc,
  decReturnType = LMVoid,
  decVarargs = FixedArgs,
  decParams = [(i8Ptr,[]),(i8,[]),(i64,[]),(i32,[]),(i1,[])],
  funcAlign = Nothing
}) Internal Nothing Nothing Constant

litNum::Integer -> LlvmType -> LlvmVar
litNum v t = LMLitVar (LMIntLit v t)

callMemset::LlvmVar -> LlvmVar -> LlvmStatement
callMemset ptr size = Expr (Call StdCall memset [ptr, litNum 0 i8, size, litNum 1 i32, litNum 0 i1] [])

newtype LocalT s m a = LocalT {runLocal:: s -> m (a, s)} --W praktyce to jest stan, ale nie chciałem mieszać z monada Translator

instance (Monad m) => Functor (LocalT s m) where
  fmap f m = m >>= (return . f)

instance (Monad m) => Applicative (LocalT s m) where
  pure = return
  f <*> a = do nf <- f
               nf <$> a

instance (Monad m) => Monad (LocalT a m) where
  return a = LocalT{ runLocal = \s -> return (a,s)}
  f >>= m = LocalT { runLocal = runLocal f >=> (\ (a, ns) -> runLocal (m a) ns)}

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

instance Eq LlvmBlock where
  a == b = (blockLabel a == blockLabel b) && (blockStmts a == blockStmts b)
  a /= b = (blockLabel a /= blockLabel b) || (blockStmts a /= blockStmts b)


mapStmtsInBlock::([LlvmStatement] -> [LlvmStatement]) -> LlvmBlock -> LlvmBlock
mapStmtsInBlock f b = b { blockStmts = f $ blockStmts b}


mapStmtInBlock::(LlvmStatement -> LlvmStatement) -> LlvmBlock -> LlvmBlock
mapStmtInBlock f = mapStmtsInBlock (map f)

replaceVars::LlvmVar -> LlvmVar -> LlvmBlock -> LlvmBlock
replaceVars from to = mapStmtInBlock (replaceVarsInStmt from to)

replaceVarsInStmts::LlvmVar -> LlvmVar -> [LlvmStatement] -> [LlvmStatement]
replaceVarsInStmts f t = map (replaceVarsInStmt f t)

replaceVarsInStmt::LlvmVar -> LlvmVar -> LlvmStatement -> LlvmStatement
replaceVarsInStmt f t (Assignment d e) = Assignment (rviv f t d) (replaceVarsInExpr f t e)
replaceVarsInStmt f t (Branch b) = Branch (rviv f t b)
replaceVarsInStmt f t (BranchIf b ift iff) = BranchIf (rviv f t b) (rviv f t ift) (rviv f t iff)
replaceVarsInStmt f t (Expr a) = Expr (replaceVarsInExpr f t a)
replaceVarsInStmt f t (Return v) = Return $ fmap (replaceVarInVar f t) v
replaceVarsInStmt f t (Store v1 v2) = Store (replaceVarInVar f t v1) (replaceVarInVar f t v2) -- do wywalenia po przejściu do SSA

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
replaceVarsInExpr f t (ExtractV s i) = ExtractV (rviv f t s) i
replaceVarsInExpr f t (InsertV s v i) = InsertV (rviv f t s) (rviv f t v) i
replaceVarsInExpr f t (Dummy v) = Dummy $ rviv f t v
replaceVarsInExpr f t (Select c ift iff) = Select (rviv f t c) (rviv f t ift) (rviv f t iff)


isSimplifiable::LlvmExpression -> Bool
isSimplifiable Dummy{} = True
isSimplifiable (LlvmOp LM_MO_SDiv _ v2) | isConst v2 && getValFromConst v2 == 0 = False
isSimplifiable (LlvmOp LM_MO_Add (LMLitVar (LMIntLit 0 _)) v) = True
isSimplifiable (LlvmOp LM_MO_Add v (LMLitVar (LMIntLit 0 _))) = True
isSimplifiable (LlvmOp LM_MO_Sub v (LMLitVar (LMIntLit 0 _))) = True
isSimplifiable (LlvmOp LM_MO_Mul (LMLitVar (LMIntLit 1 _)) v) = True
isSimplifiable (LlvmOp LM_MO_Mul v (LMLitVar (LMIntLit 1 _))) = True
isSimplifiable (LlvmOp LM_MO_SDiv v (LMLitVar (LMIntLit 1 _))) = True
isSimplifiable (LlvmOp _ v1 v2) | isConst v1 && isConst v2 = True
isSimplifiable (Compare _ v1 v2) | isConst v1 && isConst v2 = True
isSimplifiable (Compare _ v1 v2) | v1 == v2 = True
isSimplifiable (Cast LM_Sext v1 t) = isConst v1
isSimplifiable (Select c t f) = isConst c || (t == f)
isSimplifiable _ = False

isConst::LlvmVar -> Bool
isConst (LMLitVar LMIntLit{}) = True
isConst _ = False

getValFromConst::LlvmVar -> Integer
getValFromConst (LMLitVar  (LMIntLit v t)) = v

type BinOp a = a -> a -> a
type CmpOp a = a -> a -> Bool

liftOp::BinOp Integer -> BinOp LlvmVar
liftOp op v1 v2 = litNum (op (getValFromConst v1) (getValFromConst v2)) $ getVarType v1

liftCmpOp::CmpOp Integer -> BinOp LlvmVar
liftCmpOp op v1 v2 | isConst v1 && isConst v2 = litNum (if op (getValFromConst v1) (getValFromConst v2) then 1 else 0) i1
liftCmpOp op v1 v2 | v1 == v2 = litNum ( if op 0 0 then 1 else 0 ) i1

simplifyLlvmOp::LlvmMachOp -> BinOp LlvmVar
simplifyLlvmOp LM_MO_Add = liftOp (+)
simplifyLlvmOp LM_MO_Sub = liftOp (-)
simplifyLlvmOp LM_MO_Mul = liftOp (*)
simplifyLlvmOp LM_MO_SDiv = liftOp div
simplifyLlvmOp LM_MO_And = liftOp (\a b -> if (a + b) == 2 then 1 else 0)
simplifyLlvmOp LM_MO_Or = liftOp (\a b -> if (a + b) > 0 then 1 else 0)

simplifyLlvmCmp::LlvmCmpOp -> BinOp LlvmVar
simplifyLlvmCmp LM_CMP_Eq  = liftCmpOp (==)
simplifyLlvmCmp LM_CMP_Ne  = liftCmpOp (/=)
simplifyLlvmCmp LM_CMP_Sgt = liftCmpOp (>)
simplifyLlvmCmp LM_CMP_Sge = liftCmpOp (>=)
simplifyLlvmCmp LM_CMP_Slt = liftCmpOp (<)
simplifyLlvmCmp LM_CMP_Sle = liftCmpOp (<=)

simplifyExpr::LlvmExpression -> LlvmVar
simplifyExpr (Dummy v) = v
simplifyExpr (LlvmOp LM_MO_Add (LMLitVar (LMIntLit 0 _)) v) = v
simplifyExpr (LlvmOp LM_MO_Add v (LMLitVar (LMIntLit 0 _))) = v
simplifyExpr (LlvmOp LM_MO_Sub v (LMLitVar (LMIntLit 0 _))) = v
simplifyExpr (LlvmOp LM_MO_Mul (LMLitVar (LMIntLit 1 _)) v) = v
simplifyExpr (LlvmOp LM_MO_Mul v (LMLitVar (LMIntLit 1 _))) = v
simplifyExpr (LlvmOp LM_MO_SDiv v (LMLitVar (LMIntLit 1 _))) = v
simplifyExpr (LlvmOp m v1 v2) = simplifyLlvmOp m v1 v2
simplifyExpr (Compare m v1 v2) = simplifyLlvmCmp m v1 v2
simplifyExpr (Cast LM_Sext (LMLitVar (LMIntLit v _)) t) = LMLitVar $ LMIntLit v t
simplifyExpr (Select c t f) | isConst c = if getValFromConst c == 1 then t else f
simplifyExpr (Select _ t f) | t == f = t

unusedVariables::LlvmBlocks -> [LlvmVar]
unusedVariables b =
  let used = nub $ filter (not . isConst) $ usedVariablesBs b in
  let assigned = assignedVariablesBs b in
  [a | a <- assigned, a `notElem` used]

assignedVariablesBs::LlvmBlocks -> [LlvmVar]
assignedVariablesBs = flatMap assignedVariablesB

assignedVariablesB::LlvmBlock -> [LlvmVar]
assignedVariablesB b = [v | Assignment v _ <- blockStmts b]

usedVariablesBs::LlvmBlocks -> [LlvmVar]
usedVariablesBs = flatMap usedVariablesB

usedVariablesB::LlvmBlock -> [LlvmVar]
usedVariablesB = flatMap usedVariablesS . blockStmts

usedVariablesS::LlvmStatement -> [LlvmVar]
usedVariablesS (Assignment _ e) = usedVariablesE e
usedVariablesS (Expr e) = usedVariablesE e
usedVariablesS (Store f t) = [f, t]
usedVariablesS (Branch v) = [v]
usedVariablesS (BranchIf i t f) = [i, t, f]
usedVariablesS (Return v) = maybeToList v


usedVariablesE::LlvmExpression -> [LlvmVar]
usedVariablesE (GetElemPtr _ p a) = p : a
usedVariablesE (Call _ f a _) = f : a
usedVariablesE (Compare _ f s) = [f, s]
usedVariablesE (LlvmOp _ f s) = [f, s]
usedVariablesE (Load p) = [p]
usedVariablesE (Cast _ v _) = [v]
usedVariablesE (Phi _ p) = let (v,l) = unzip p in v ++ l
usedVariablesE (ExtractV s _) = [s]
usedVariablesE (InsertV s v _) = [s, v]
usedVariablesE (Select c t f) = [c, t, f]

isReturn::LlvmStatement -> Bool
isReturn Return{} = True
isReturn _ = False