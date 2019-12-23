{-# LANGUAGE TupleSections #-}
module Compiler.LlvmSimplifier where

import Llvm
import Data.List
import Common.Utils
import Compiler.ILTransformerCommon
import Compiler.PhiPropagator
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe
import Control.Lens
import Debug.Trace

simplifyLlvm::LlvmBlocks -> LlvmBlocks
simplifyLlvm = untilStabilize (globalCommonSimplification . simplifyConstants . removeSingleValuePhis)

-- przy przekształcaniu do ssa potrafią powstać %v = phi [%v, %1], [%c, %3] więc podmieniamy %v na %c 
removeSingleValuePhis::LlvmBlocks -> LlvmBlocks
removeSingleValuePhis bs =
  let allStmts = flatMap blockStmts bs in
  let stmtsToRemove = [a | a@(Assignment r (Phi _ v)) <- allStmts, length (nub $ filter (/= r) $ fst <$> v) == 1] in
  if null stmtsToRemove then bs
  else -- usuwamy pojedynczo żeby niczego nie napsuć, wszystko na raz potrafi napsuć niestety :)
    let currentRm@(Assignment r (Phi _ v)) = head stmtsToRemove in
    let toReplace = head $ nub $ filter (/= r) $ fst <$> v in
    let newBs = map (mapStmtsInBlock $ filter (/= currentRm)) bs in
    let finalBs = map (replaceVars r toReplace) newBs in
    removeSingleValuePhis finalBs

simplifyConstants::LlvmBlocks -> LlvmBlocks
simplifyConstants b =
  let allStmts = flatMap blockStmts b in
  let toSimplify = [(v, simplifyExpr e, a) | a@(Assignment v e) <- allStmts, isSimplifiable e] in
  case toSimplify of
    [] -> b --pojedynczo żeby nie zepsuć
    ((old, toRep, stmtToRm): _) ->
                              let newB = map (mapStmtsInBlock $ filter (/= stmtToRm)) b in
                              let finalB = map (replaceVars old toRep) newB in
                              simplifyConstants finalB


-- usuwanie wspólnych podwyrażeń w całym ciele funkcji
globalCommonSimplification::LlvmBlocks -> LlvmBlocks
globalCommonSimplification b =
  let propagationInfo = buildPropagationInfo b in
  let dominatingElems = map (\i-> (i, getDominatingBlocks i propagationInfo)) [2..(length b)] in
  let simpl = globalCommonS propagationInfo dominatingElems (S.singleton 1) in
  M.elems $ _blocks simpl
  where globalCommonS prop toDo done =
          let toProcess = filter (\(_,r) -> S.isSubsetOf r done) toDo in
          case toProcess of
            [] -> prop
            ((i,r):_) -> let pblocks = M.elems $ M.restrictKeys (_blocks prop) r in
                         let correctAssigns = filter correctStmts $ flatMap blockStmts pblocks in
                         let map = [(v,e) | Assignment v e <- correctAssigns] in
                         let procBlock = _blocks prop M.! i in
                         let reducibleStmts = [(a, nv, fst $ head $ filter (( == ne) . snd) map)
                                | a@(Assignment nv ne) <- blockStmts procBlock, any (( == ne) . snd) map] in
                         case reducibleStmts of
                           [] -> globalCommonS prop (filter ((/= i) . fst) toDo) (S.insert i done)
                           ((a, old, n):_) -> let nBlock = procBlock {blockStmts = filter (/= a) $ blockStmts procBlock} in
                                              let rProp = prop & (blocks %~ M.insert i nBlock) in
                                              let fProp = rProp & (blocks %~ M.map (replaceVars old n)) in
                                              globalCommonS fProp toDo done

        correctStmts (Assignment _ e) = correctExprs e
        correctStmts _ = False
        correctExprs Alloca{} = False
        correctExprs Load{} = False
        correctExprs Phi{} = False
        correctExprs Call{} = False
        correctExprs _ = True


buildPropagationInfo::LlvmBlocks -> PropagationInfo
buildPropagationInfo bs =
   let withInt = zip [1 .. (length bs)] bs in
   let vi = map (\(i,b) -> (blockLabel b, i)) withInt in
   let succs = map (\(i,b) -> (i, map (\u -> snd $ getFirstSure (( == u) . fst) vi) $ getSuccessors b)) withInt in
   let preds = M.fromList $ groupByFirst $ map (\(a,b) -> (b,a)) $ flatMap (\(u,l) -> (u,) <$> l) succs in
   let withNoPred = M.fromList $ (, ()) <$> filter (not . (`M.member` preds)) (fst <$> tail withInt) in
   let withIntFiltered = filter (\(i,_) -> M.member i preds  || i == 1) withInt in
   let mapped = M.fromList withIntFiltered in
   PropagationInfo {
     _entry = 1,
     _blocks = mapped,
     _preds = M.map (filter (\ e -> not $ M.member e withNoPred)) preds,
     _succs = M.filterWithKey (\k _ -> M.member k preds || k == 1) $ M.fromList succs,
     _imports = M.empty,
     _exports = M.empty,
     _requires = M.empty
   }


getDominatingBlocks::Int -> PropagationInfo -> S.Set Int
getDominatingBlocks i p =
  let paths = tail <$> getSimplePathsToEntry i p in
  let sets = map S.fromList paths in
  let common = foldl1 S.intersection sets in
  common


getSimplePathsToEntry::Int -> PropagationInfo -> [[Int]]
getSimplePathsToEntry i p =
  if _entry p == i then [[i]]
  else helpF i p []
       where helpF i p visited
               | i `elem` visited = []
               | _entry p == i = [[i]]
               | otherwise =
                   let preds = _preds p M.! i in
                   let paths = flatMap (((i :) <$>) . (\c -> helpF c p (i : visited))) preds in
                   paths
