{-# LANGUAGE TupleSections #-}
module Compiler.LlvmSimplifier where

import MyLlvm.Llvm
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
simplifyLlvm = untilStabilize (
    removeEmptyBlocks .
    removeUnusedVariables .
    compactBlocks .
    globalCommonSimplification .
    simplifyConstants .
    removeSingleValuePhis
  )

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
                         let inserts = [(v, ExtractV a (fromInteger $ head i)) | Assignment a (InsertV _ v i) <- correctAssigns] in
                         let map = [(v,e) | Assignment v e <- correctAssigns] ++ inserts in
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



compactBlocks::E LlvmBlocks
compactBlocks b =
  let pInfo = buildPropagationInfo b in
  let withSinglePred = _preds pInfo & M.filter ((== 1) . length) & M.map head in
  let alsoWithSingleSucc = M.toList $ M.filter (\p -> _succs pInfo M.! p & length & (==) 1) withSinglePred in
  case alsoWithSingleSucc of
    [] -> b
    (s,p) : _ -> let sBlock = _blocks pInfo M.! s in
                 let pBlock = _blocks pInfo M.! p in
                 let pBody = blockStmts pBlock in
                 let sBody = blockStmts sBlock in
                 let joined = pBlock {blockStmts = init pBody ++ sBody } in
                 let nProp = pInfo & blocks %~ M.filterWithKey (\ k _ -> k /= s) . M.insert p joined in
                 let fBlocks = M.elems $ M.map (replaceVars (varLabel sBlock) (varLabel pBlock)) $ _blocks nProp in
                 compactBlocks fBlocks
  where varLabel block = LMLocalVar (blockLabel block) LMLabel


removeUnusedVariables::E LlvmBlocks
removeUnusedVariables b =
  let unused = unusedVariables b in
  case unused of
    [] -> b
    a:_ -> let mapped = map (mapStmtInBlock (removeAssignment a)) b in
           let removedNops = map (mapStmtsInBlock (filter ( /= Nop))) mapped in
           removeUnusedVariables removedNops
  where removeAssignment v (Assignment av c@Call{}) | v == av = Expr c
        removeAssignment v (Assignment av _) | v == av = Nop
        removeAssignment _ s = s

-- TODO fix, potrafią rozwalić ify, zastąpić przez select jeśli mi się chce
removeEmptyBlocks::E LlvmBlocks
removeEmptyBlocks b =
  let pInfo = buildPropagationInfo b in
  let usedVars = flatMap usedVariablesS [a | a@(Assignment _ Phi{}) <- flatMap blockStmts b] in
  let emptyBlocks = [(e,i, t, l, used, preds) | (i, e) <- M.toList $ _blocks pInfo,
                                           [Branch t] <- [blockStmts e],
                                           l <- [LMLocalVar (blockLabel e) LMLabel],
                                           used <- [l `elem` usedVars],
                                           preds <- [fromMaybe [] $ _preds pInfo M.!? i ] ] in
  let filtered = filter (\(_,_,_,_,u,p) -> not u) emptyBlocks in
  case filtered of
    [] -> b
    (e,i,t,l,False, _):_ -> let nBlocks = _blocks pInfo & M.filterWithKey(\k _ -> k /= i) & M.elems in
                            let repl = map (replaceVars l t) nBlocks in
                            removeEmptyBlocks repl
    (e,i,t,l,True, [p]):_ -> let nBlocks = _blocks pInfo & M.filterWithKey(\k _ -> k /= i) & M.elems in
                             let pBlockLabel = LMLocalVar (_blocks pInfo M.! p & blockLabel) LMLabel in
                             let repl = map (mapStmtInBlock (replaceInPhi l pBlockLabel . replaceInReturn l t)) nBlocks in
                             removeEmptyBlocks repl
  where replaceInReturn f t (Branch v) = Branch (replaceVarInVar f t v)
        replaceInReturn f t (BranchIf c ift iff) = BranchIf c (replaceVarInVar f t ift) (replaceVarInVar f t iff)
        replaceInReturn _ _ s = s
        replaceInPhi f t a@(Assignment _ Phi{}) = replaceVarsInStmt f t a
        replaceInPhi _ _ a = a


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

