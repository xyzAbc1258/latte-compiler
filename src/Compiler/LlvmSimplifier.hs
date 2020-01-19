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
import Debug.Trace hiding(traceShow)
import Unique (getUnique)
import FastString (appendFS)

simplifyLlvm::E LlvmBlocks
simplifyLlvm = untilStabilize (
    removeUnusedVariables .
    removeUnreachableBlocks .
    simplifyBranching .
    compactBlocks .
    globalCommonSimplification .
    simplifyConstants .
    removeSingleValuePhis
  )

-- przy przekształcaniu do ssa potrafią powstać %v = phi [%v, %1], [%c, %3] więc podmieniamy %v na %c 
removeSingleValuePhis::E LlvmBlocks
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

simplifyConstants::E LlvmBlocks
simplifyConstants b =
  let allStmts = flatMap blockStmts b in
  let toSimplify = [(v, simplifyExpr e, a) | a@(Assignment v e) <- allStmts, isSimplifiable e] in
  case toSimplify of
    [] -> b --pojedynczo żeby nie zepsuć
    ((old, toRep, stmtToRm): _) ->
                              let newB = map (mapStmtsInBlock $ filter (/= stmtToRm)) b in
                              let finalB = map (replaceVars old toRep) newB in
                              simplifyConstants finalB


removeUnreachableBlocks::E LlvmBlocks
removeUnreachableBlocks b =
  let p = buildPropagationInfo b in
  let unreachable = p ^. blocks & M.keys & filter (\k -> k /= 1 && isNothing (_preds p M.!? k)) in --bez poprzedników niebędące entry 
  if null unreachable then b
  else
    let reachable = p ^. blocks & M.filterWithKey (\k _ -> k `notElem` unreachable) & M.elems in
    let labelsToRem = map (blockLabel . (_blocks p M.!)) unreachable in
    let withCorrectedPhis = map (mapStmtInBlock (fixPhis labelsToRem)) reachable in
    removeUnreachableBlocks withCorrectedPhis
  where fixPhis toRem (Assignment v (Phi t l)) = Assignment v (Phi t [p | p@(_, LMLocalVar id LMLabel) <- l, id `notElem` toRem])
        fixPhis _ s = s


simplifyBranching::E LlvmBlocks
simplifyBranching = map simplHelp 
  where simplHelp b | last (blockStmts b) & isReturn & not = 
          case last (blockStmts b) of
               BranchIf c ift iff | isConst c && getValFromConst c == 0 -> b {blockStmts = init (blockStmts b) ++ [Branch iff]}
               BranchIf c ift iff | isConst c && getValFromConst c == 1 -> b {blockStmts = init (blockStmts b) ++ [Branch ift]}
               BranchIf c ift iff | ift == iff -> b {blockStmts = init (blockStmts b) ++ [Branch iff]}
               _ -> b 
        simplHelp b = b
        
-- usuwanie wspólnych podwyrażeń w całym ciele funkcji
globalCommonSimplification::E LlvmBlocks
globalCommonSimplification b =
  let propagationInfo = buildPropagationInfo b in
  let dominatingElems = map (\i-> (i, getDominatingBlocks i propagationInfo)) (filter (/= 1) $ M.keys $ _blocks propagationInfo) in
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
                         let procBlock = _blocks prop `getFMapI` i in
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
  let alsoWithSingleSucc = M.toList $ M.filter (\p -> _succs pInfo `getFMapI` p & length & (==) 1) withSinglePred in
  case alsoWithSingleSucc of
    [] -> b
    (s,p) : _ -> let sBlock = _blocks pInfo `getFMapI` s in
                 let pBlock = _blocks pInfo `getFMapI` p in
                 let pBody = blockStmts pBlock in
                 let sBody = blockStmts sBlock in
                 let joined = pBlock {blockStmts = init pBody ++ sBody } in
                 let nProp = pInfo & blocks %~ M.filterWithKey (\ k _ -> k /= s) . M.insert p joined in
                 let fBlocks = M.elems $ M.map (replaceVars (varLabel sBlock) (varLabel pBlock)) $ _blocks nProp in -- naprawia phi po usunięciu bloku
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
     _blocks = M.fromList withInt,--mapped,
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
  if null sets then S.empty
  else foldl1 S.intersection sets


getSimplePathsToEntry::Int -> PropagationInfo -> [[Int]]
getSimplePathsToEntry i p =
  if _entry p == i then [[i]]
  else helpF i p []
       where helpF i p visited
               | i `elem` visited = []
               | _entry p == i = [[i]]
               | otherwise =
                   let preds = fromMaybe [] $ _preds p M.!? i in
                   let paths = flatMap (((i :) <$>) . (\c -> helpF c p (i : visited))) preds in
                   paths


tailCallOptimization::E LlvmFunction
tailCallOptimization f =
  if not $ isTailCallOptimizable f then f
  else let body = funcBody f in
       let fName = decName (funcDecl f) in
       let funcParams = zipWith LMNLocalVar (funcArgs f) (map fst $ decParams $ funcDecl f) in
       let retBlocks = filter (isReturn . last . blockStmts) body in
       let retValues = nub $ flatMap (maybeToList . (\(Return v) -> v) . last . blockStmts) retBlocks in
       let retVTailCalls = [(b, a, args) | (b, a@(Assignment v (Call _ (LMGlobalVar _ (LMFunction d) _ _ _ _) args _)))
                                   <- flatMap (\b -> (b,) <$> blockStmts b) retBlocks, v `elem` retValues, decName d == fName] in
       let nEntry = getUnique $ mkfs "nEntry" in
       let fEntry = getUnique $ mkfs "tailEntry" in
       let phiNames = map (\(LMNLocalVar n t) -> LMNLocalVar (appendFS n (mkfs "_phi")) t) funcParams in
       let allToPhi = (nEntry, funcParams) : map (\(b,_,args) -> (blockLabel b, args)) retVTailCalls in
       let phiSources = map (\ (a,p) -> (,makeLabelVar a) <$> p) allToPhi in
       let phis = zipWith (\t l -> Assignment t $ Phi (getVarType t) l) phiNames (invertList phiSources) in
       let stmtsToRemove = map (\(_,s,_) -> s) retVTailCalls in
       let rBlocks = nub $ map (\(b,_,_) -> blockLabel b) retVTailCalls in
       let woCalls = map (mapStmtsInBlock (filter (`notElem` stmtsToRemove))) body in
       let nBodyWithReplVars = foldl (flip (<$>)) woCalls $ zipWith replaceVars funcParams phiNames in
       let withJumps = map (replaceToJump rBlocks fEntry) nBodyWithReplVars in
       let firstBlock = LlvmBlock {blockLabel = nEntry, blockStmts = [Branch (LMLocalVar fEntry LMLabel)]} in
       let sndBlock = LlvmBlock {blockLabel = fEntry, blockStmts = phis ++ [Branch (makeLabelVar (blockLabel $ head withJumps))]} in
       f {funcBody = simplifyLlvm $ firstBlock : sndBlock : withJumps}
       where replaceToJump ids target b | blockLabel b `notElem` ids = b
             replaceToJump _ target b = b {blockStmts = init (blockStmts b) ++ [Branch (makeLabelVar target)]}
             makeLabelVar t = LMLocalVar t LMLabel

isTailCallOptimizable::LlvmFunction -> Bool
isTailCallOptimizable f =
  let body = funcBody f in
  let retBlocks = filter (isReturn . last . blockStmts) body in
  let retValues = nub $ flatMap (maybeToList . (\(Return v) -> v) . last . blockStmts) retBlocks in
  let retVTailCalls = [() | Assignment v (Call _ (LMGlobalVar _ (LMFunction d) _ _ _ _) _ _)
                            <- flatMap blockStmts retBlocks, v `elem` retValues, decName d == decName (funcDecl f)] in
  let allCallsToItself = [() | Assignment v (Call _ (LMGlobalVar _ (LMFunction d) _ _ _ _) _ _)
                            <- flatMap blockStmts body, v `elem` retValues, decName d == decName (funcDecl f)] in
  (length retVTailCalls == length allCallsToItself && not (null retVTailCalls))