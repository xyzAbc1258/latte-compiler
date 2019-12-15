{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Compiler.PhiPropagator where

import Llvm
import Data.List
import Control.Monad
import Common.Utils
import qualified Data.Map as M
import Unique (Unique)
import Compiler.ILTransformerCommon
import Data.Maybe
import Control.Applicative((<|>))
import System.IO.Unsafe (unsafePerformIO)
import Debug.Trace (traceM, trace)
import Outputable (showSDocUnsafe)

data PropagationInfo = PropagationInfo {
      _entry :: Int,
      _blocks:: M.Map Int LlvmBlock,
      _preds :: M.Map Int [Int],
      _succs :: M.Map Int [Int],
      _imports:: M.Map Int (Maybe LlvmVar),
      _exports:: M.Map Int (Maybe LlvmVar),
      _requires:: M.Map Int Bool
    } deriving (Eq, Show)

instance Eq LlvmBlock where
  a == b = (blockLabel a == blockLabel b) && (blockStmts a == blockStmts b)
  a /= b = (blockLabel a /= blockLabel b) || (blockStmts a /= blockStmts b)

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
  let splitted = trace ("splitted" ++ (show $ map length spl)) spl in
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

instance Show LlvmBlock where
  show b = show (blockLabel b)

instance Show LlvmVar where
  show v = showSDocUnsafe $ ppName v

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
    _preds = M.map (\l -> filter (\e -> not $ M.member e withNoPred) l) $ preds,
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


untilStabilize::(Eq a ,Monad m) => (a -> m a) -> a -> m a
untilStabilize f a = do
  r <- f a
  if r /= a then untilStabilize f r
  else return r

propagatePhiForVar::LlvmVar -> PropagationInfo -> Translator PropagationInfo
propagatePhiForVar v p= untilStabilize main p
  where helpP p = do
                    r <- untilStabilize (simplePropagateVar v) p
                    untilStabilize (multiPredPropagation v) r
        main p = do
                    r <- untilStabilize helpP p
                    let requiring = M.keys $ M.filter id $  _requires r
                    let allSatisfied = all (isJust . (_imports r M.!)) requiring
                    if allSatisfied then return $ r {_blocks = M.map (filterOutAllocStoreFromBlock v) $ _blocks r}
                    else cheatNexuses v r
                           

simplePropagateVar::LlvmVar -> PropagationInfo -> Translator PropagationInfo
simplePropagateVar v p = do
  let canPropagate = M.keys $ M.filter isJust $ _exports p
  let withSinglePred = M.map head $  M.filter (( == 1) . length) $ _preds p
  let importsAny = M.map isJust $ _imports p
  let canBePropagated = M.filterWithKey (\k v -> v `elem` canPropagate && not (importsAny M.! k)) withSinglePred
  let valPropagation = M.toList $ M.map (fromJust . (_exports p M.!)) canBePropagated
  let np = foldl (\cp (i,nv) -> fixSimplePropagation v i nv cp) p valPropagation
  return np

fixSimplePropagation::LlvmVar -> Int -> LlvmVar -> PropagationInfo -> PropagationInfo
fixSimplePropagation v i nv p =
  let doesIrequire = _requires p M.! i in
  if not doesIrequire then
    p {_imports = M.insert i (Just nv) $ _imports p, _exports = M.adjust (<|> Just nv) i $ _exports p}
  else let block = _blocks p M.! i in
       let (b,f, used) = splitOnLoad v $ blockStmts block in
       let nBlock = block {blockStmts = b ++ replaceVarsInStmts used nv f } in
       p {
          _blocks = M.adjust (const nBlock) i $ _blocks p,
          _imports = M.insert i (Just nv) $ _imports p,
          _exports = M.adjust (<|> Just nv) i $ _exports p
       }

multiPredPropagation::LlvmVar -> PropagationInfo -> Translator PropagationInfo
multiPredPropagation v p = do
  let withPreds = M.keys $ _preds p
  let requireWithPreds = filter (isNothing . (_imports p M.!)) withPreds
  let allPredsHas = filter (\i -> all (isJust . (_exports p M.!)) $ _preds p M.! i ) requireWithPreds
  foldl (\cp i -> cp >>= (addPhi v i)) (return p) allPredsHas
  where addPhi v i cp = do
          let preds = _preds cp M.! i
          let values = map (\pi -> (pi, fromJust $ _exports cp M.! pi)) preds
          let requiresVar = _requires cp M.! i
          if (length $ nub $ snd <$> values) == 1 then do
            let newVari = head $ nub $ snd <$> values
            let block = _blocks cp M.! i
            let nBlock = if requiresVar then
                                          let (b,a, vl) = splitOnLoad v (blockStmts block) in
                                          let nAfter = replaceVarsInStmts vl newVari a in
                                          block {blockStmts = b ++ nAfter}
                                        else block
            return $ cp {
              _blocks = M.adjust (const nBlock) i $ _blocks cp,
              _imports = M.insert i (Just newVari) $ _imports cp,
              _exports = M.adjust ( <|> Just newVari) i $ _exports cp
            }
          else do
            let block = _blocks cp M.! i
            let phiValues = map (\(i,v) -> (v,flip LMLocalVar LMLabel $ blockLabel (_blocks cp M.! i))) values
            (nBlock,vl) <- if requiresVar then
                                          let (b,a, vl) = splitOnLoad v (blockStmts block) in
                                          let assign = Assignment vl $ Phi (getVarType vl) phiValues in
                                          return (block {blockStmts = [assign] ++  b ++ a}, vl)
                                        else do
                                          nVar <- newVar $ getVarType $ snd $ head values
                                          let assign = Assignment nVar $ Phi (getVarType nVar) phiValues
                                          return (block {blockStmts = assign : blockStmts block}, nVar)
            return $ cp {
             _blocks = M.adjust (const nBlock) i $ _blocks cp,
             _imports = M.insert i (Just vl) $ _imports cp,
             _exports = M.adjust ( <|> Just vl) i $ _exports cp
            }

findLoad::LlvmVar -> LlvmBlock -> Maybe LlvmVar
findLoad v b =
  let s = getFirst isLoad $ blockStmts b in
  case s of
    Just (Assignment d _) -> Just d
    Nothing -> Nothing
  where isLoad (Assignment _ (Load v1)) = v1 == v
        isLoad _ = False

cheatNexuses::LlvmVar -> PropagationInfo -> Translator PropagationInfo
cheatNexuses v p = do
  let withPreds = M.keys $ _preds $ trace ("cheat: " ++ show p) p
  let notExportingAndNotImporting = filter (\s -> any isJust ((_exports p M.!) <$> (_preds p M.! s)) && isNothing (_imports p M.! s) && isNothing (_exports p M.! s)) withPreds
  let forwardWhile = filter (\ s -> (1 ==) $ length $ nub $ map fromJust $ filter isJust ((_exports p M.!) <$> (_preds p M.! s))) notExportingAndNotImporting
  let mappedForward =M.fromList $  map (\ s -> (s,head $ map fromJust $ filter isJust ((_exports p M.!) <$> (_preds p M.! s)))) forwardWhile
  let loaded = (\i -> (i, findLoad v (_blocks p M.! i) <|> (mappedForward M.!? i))) <$> notExportingAndNotImporting
  let exports = _exports p
  let nExp1 = foldl (\c (i, v) -> M.insert i v c) exports loaded
  let nExp = trace ("cheating: " ++ show nExp1) nExp1
  return p {_exports = nExp}


cheatNexuses2::LlvmVar -> PropagationInfo -> Translator PropagationInfo
cheatNexuses2 v p = do
  let withPreds = M.keys $ _preds $ trace ("cheat: " ++ show p) p
  let notExportingAndNotImporting = filter (\s -> any isJust ((_exports p M.!) <$> (_preds p M.! s)) && isNothing (_imports p M.! s) && isNothing (_exports p M.! s)) withPreds
  let forwardWhile = filter (\ s -> (1 <) $ length $ nub $ map fromJust $ filter isJust ((_exports p M.!) <$> (_preds p M.! s))) notExportingAndNotImporting
  let mappedForward =M.fromList $  map (\ s -> (s,head $ map fromJust $ filter isJust ((_exports p M.!) <$> (_preds p M.! s)))) forwardWhile
  let loaded = (\i -> (i, findLoad v (_blocks p M.! i) <|> (mappedForward M.!? i))) <$> notExportingAndNotImporting
  let exports = _exports p
  let nExp1 = foldl (\c (i, v) -> M.insert i v c) exports loaded
  let nExp = trace ("cheating: " ++ show nExp1) nExp1
  return p {_exports = nExp}

getSuccessors::LlvmBlock -> [Unique]
getSuccessors b =
  let lastStmt = last $ blockStmts b in
  case lastStmt of
    Return{} -> []
    Branch (LMLocalVar r _) -> [r]
    BranchIf _ (LMLocalVar r1 _) (LMLocalVar r2 _) -> [r1, r2]