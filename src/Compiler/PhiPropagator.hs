{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
module Compiler.PhiPropagator where

import Llvm
import Data.List
import Control.Monad
import Common.Utils
import qualified Data.Map as M
import Unique (Unique)
import Compiler.ILTransformerCommon
import Data.Maybe
import Control.Applicative((<|>), Alternative)
import System.IO.Unsafe (unsafePerformIO)
import Debug.Trace (traceM, trace)
import Outputable (showSDocUnsafe)
import Control.Monad.Fix
import Control.Lens
import Data.Function

instance Show LlvmBlock where
  show b = show (blockLabel b)

instance Show LlvmVar where
  show v = showSDocUnsafe $ ppName v

instance Eq LlvmBlock where
  a == b = (blockLabel a == blockLabel b) && (blockStmts a == blockStmts b)
  a /= b = (blockLabel a /= blockLabel b) || (blockStmts a /= blockStmts b)


data PropagationInfo = PropagationInfo {
      _entry :: Int,
      _blocks:: M.Map Int LlvmBlock,
      _preds :: M.Map Int [Int],
      _succs :: M.Map Int [Int],
      _imports:: M.Map Int (Maybe LlvmVar),
      _exports:: M.Map Int (Maybe LlvmVar),
      _requires:: M.Map Int Bool
    } deriving (Eq, Show)

$(makeLenses ''PropagationInfo)

type ME a = a -> Translator a
type MEProp = ME PropagationInfo

fst3 (x,_,_) = x
snd3 (_,x,_) = x
thd3 (_,_,x) = x


getFirst::(a -> Bool) -> [a] -> Maybe a
getFirst _ [] = Nothing
getFirst f (h:t) | f h = Just h
getFirst f (_:t) = getFirst f t

getFirstSure f s = let (Just r) = getFirst f s in r

splitOnLoad::LlvmVar -> [LlvmStatement] -> ([LlvmStatement], [LlvmStatement], LlvmVar)
splitOnLoad v l =
  let spl = splitOn isLoad l in
  let splitted = spl in
  if length splitted == 2 then
    let [[Assignment v _], a] = splitted in
    ([],a, v)
  else
    let [b,[Assignment v _], a] = splitted in
    (b, a, v)
    where isLoad (Assignment _ (Load dest)) = dest == v
          isLoad _ = False

filterOutAllocStoreFromBlock::LlvmVar -> LlvmBlock -> LlvmBlock
filterOutAllocStoreFromBlock v b = b {blockStmts = filter (filterOutAllocStore v) $ blockStmts b}

filterOutAllocStore::LlvmVar -> LlvmStatement -> Bool
filterOutAllocStore v1 (Assignment v2 Alloca{}) = v1 /= v2
filterOutAllocStore v1 (Store _ v2) = v1 /= v2
filterOutAllocStore _ _ = True

propagatePhi::[(LlvmBlock, [LlvmVar], [(LlvmVar, LlvmVar)])] -> Translator LlvmBlocks
propagatePhi l = do
  let allToPropagate = nub $ join $ map (\(_,v,_) -> v) l
  let withInt = zip [1 .. (length l)] l
  let vi = map (\(i,(b,_,_)) -> (blockLabel b, i)) withInt
  let succs = map (\(i,(b,_,_)) -> (i, map (\u -> snd $ getFirstSure (( == u) . fst) vi) $ getSuccessors b)) withInt
  let preds = M.fromList $ groupByFirst $ map (\(a,b) -> (b,a)) $ join $ map (\(u,l) -> (u,) <$> l) succs
  let withNoPred = M.fromList $ (, ()) <$> filter (not . (`M.member` preds)) (fst <$> tail withInt)
  let withIntFiltered = filter (\(i,_) -> M.member i preds  || i == 1) withInt
  let mapped = M.fromList $ map (\(i,(b,_,_)) -> (i,b)) withIntFiltered
  let processVariable v = propagatePhiForVar v . forVariable withIntFiltered v
  let empty = PropagationInfo {
    _entry = 1,
    _blocks = mapped,
    _preds = M.map (filter (\ e -> not $ M.member e withNoPred)) preds,
    _succs = M.filterWithKey (\k _ -> M.member k preds || k == 1) $ M.fromList succs,
    _imports = M.empty,
    _exports = M.empty,
    _requires = M.empty
  }
  (snd <$>) . M.toList . _blocks <$> foldl (\ p v -> p >>= processVariable v) (return empty) allToPropagate
  where forVariable wInt v prop =
            let requires = M.fromList $ map (\(i,(_,r,_)) -> (i,v `elem` r)) wInt in
            let exports = M.fromList $ map (\(i,(_,_,e)) -> (i,snd <$> getFirst (( == v) . fst) e)) wInt in
            prop {_requires = requires, _exports = exports, _imports = M.map (const Nothing) requires}


untilStabilize::(Eq a ,Monad m) => (a -> m a) -> a -> m a -- poor man's fix :)
untilStabilize f a = do
  r <- f a
  if r /= a then untilStabilize f r
  else return r

propagatePhiForVar::LlvmVar -> MEProp
propagatePhiForVar v = untilStabilize main
  where main p = do
                    let requiring = M.keys $ M.filter id $  _requires p
                    sp <- untilStabilize (simplePropagateVar v) p
                    finalP <- foldM (\p i ->fst <$> getImportValue v i p) sp requiring
                    let allSatisfied = all (isJust . (_imports finalP M.!)) requiring
                    if allSatisfied then return $ finalP & blocks %~ M.map (filterOutAllocStoreFromBlock v)
                    else
                      return finalP
                           

simplePropagateVar::LlvmVar -> MEProp
simplePropagateVar v p = do
  let canPropagate = M.keys $ M.filter isJust $ _exports p
  let withSinglePred = M.map head $  M.filter (( == 1) . length) $ _preds p
  let importsAny = M.map isJust $ _imports p
  let canBePropagated = M.filterWithKey (\k v -> v `elem` canPropagate && not (importsAny M.! k)) withSinglePred
  let valPropagation = M.toList $ M.map (fromJust . (_exports p M.!)) canBePropagated
  let np = foldl (\cp (i,nv) -> fixSimplePropagation v i nv cp) p valPropagation
  return np

fixSimplePropagation::LlvmVar -> Int -> LlvmVar -> E PropagationInfo
fixSimplePropagation v i nv p =
  let doesIrequire = _requires p M.! i in
  if not doesIrequire then
    p & addToMap imports i (Just nv) & adjustMap exports i (Just nv)
  else let block = _blocks p M.! i in
       let (b,f, used) = splitOnLoad v $ blockStmts block in
       let nBlock = block {blockStmts = b ++ replaceVarsInStmts used nv f } in
       updateB i nBlock (Just nv) (Just nv) p & blocks %~ M.map (replaceVars used nv)


getImportValue::LlvmVar -> Int -> PropagationInfo -> Translator (PropagationInfo, LlvmVar)
getImportValue v i p = case _imports p M.! i of
                         Just e -> return (p,e)
                         _ ->
                           do
                              let requiresVar = _requires p M.! i
                              let preds = _preds p M.! i
                              varCand <- newVar (getVarType $ pVarLower v)
                              (fp, sValues) <- foldM (\(cp,l) i -> (\(a,b) -> (a,b:l)) <$> getExportValue v i cp) (adjustExport i (Just varCand) p,[]) preds
                              let values = zip (reverse preds) sValues
                              (np, ve) <-  if length (nub $ snd <$> values) == 1 then
                                               do let newVari = head $ nub $ snd <$> values
                                                  let block = _blocks fp M.! i
                                                  let (nBlock,oldV)
                                                        = if requiresVar then
                                                            let (b, a, vl) = splitOnLoad v (blockStmts block) in
                                                              let nAfter = replaceVarsInStmts vl newVari a in
                                                                (block{blockStmts = b ++ nAfter},vl)
                                                            else (block, newVari)
                                                  let upd = updateB i nBlock (Just newVari) (Just newVari) fp
                                                  let allUpd = upd & blocks %~ M.map (replaceVars oldV newVari)
                                                  return (allUpd, newVari)
                                               else
                                               do let block = _blocks fp M.! i
                                                  let phiValues
                                                        = map
                                                            (\ (i, v) ->
                                                               (v,
                                                                flip LMLocalVar LMLabel $ blockLabel $ _blocks fp M.! i))
                                                            values
                                                  (nBlock, vl, oldV) <- if requiresVar then
                                                                    let (b, a, vl) = splitOnLoad v (blockStmts block) in
                                                                      let assign
                                                                            = Assignment varCand $
                                                                                Phi (getVarType vl) phiValues
                                                                        in
                                                                        return
                                                                          (block{blockStmts = [assign] ++ b ++ replaceVarsInStmts vl varCand a}, varCand, vl)
                                                                    else
                                                                    do let nVar = varCand
                                                                       let assign
                                                                             = Assignment nVar $
                                                                                 Phi (getVarType nVar) phiValues
                                                                       return
                                                                         (block{blockStmts = assign : blockStmts block}, nVar, nVar)
                                                  return (updateB i nBlock (Just vl) (Just vl) fp & blocks %~ M.map (replaceVars oldV vl), vl)
                              if varCand /= ve then
                                return
                                  (np & blocks %~ M.map (replaceVars varCand ve) & 
                                    exports %~ M.map (\e -> if e == Just varCand then Just ve else e), ve)
                              else return (np, ve)

getExportValue::LlvmVar -> Int -> PropagationInfo -> Translator (PropagationInfo, LlvmVar)
getExportValue v i p = case _exports p M.! i of
                           Just e -> return (p, e)
                           _ -> do (np, imp) <- getImportValue v i p
                                   return (adjustExport i (Just imp) np, imp)

updateB::Int -> LlvmBlock ->Maybe LlvmVar ->Maybe LlvmVar -> E PropagationInfo
updateB i nBlock imp exp cp =
  cp {
      _blocks = M.adjust (const nBlock) i $ _blocks cp,
      _imports = M.insert i imp $ _imports cp,
      _exports = M.adjust ( <|> exp) i $ _exports cp
    }

findLoad::LlvmVar -> LlvmBlock -> Maybe LlvmVar
findLoad v b =
  let s = getFirst isLoad $ blockStmts b in
  case s of
    Just (Assignment d _) -> Just d
    Nothing -> Nothing
  where isLoad (Assignment _ (Load v1)) = v1 == v
        isLoad _ = False

getSuccessors::LlvmBlock -> [Unique]
getSuccessors b =
  let lastStmt = last $ blockStmts b in
  case lastStmt of
    Return{} -> []
    Branch (LMLocalVar r _) -> [r]
    BranchIf _ (LMLocalVar r1 _) (LMLocalVar r2 _) -> [r1, r2]


adjustMap::(Ord k, Alternative v) => Lens' PropagationInfo (M.Map k (v a)) -> k -> v a -> E PropagationInfo
adjustMap l i v = over l (M.adjust (<|> v) i)

adjustExport::Int -> Maybe LlvmVar -> E PropagationInfo
adjustExport = adjustMap exports

addExport::Int->Maybe LlvmVar -> E PropagationInfo
addExport = addToMap exports

addToMap::(Ord k) => Lens' PropagationInfo (M.Map k v) -> k -> v -> E PropagationInfo
addToMap l i v = over l (M.insert i v)

