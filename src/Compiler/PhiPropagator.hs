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
  let [a, b] = splitOn isLoad l in
  let (Assignment v _ : _) = drop (length a) l
  in (a,b, v)
    where isLoad (Assignment _ (Load dest)) = dest == v
          isLoad _ = False
propagatePhi::[(LlvmBlock, [LlvmVar], [(LlvmVar, LlvmVar)])] -> Translator LlvmBlocks
propagatePhi l = return $ map fst3 l


-- propagatePhi::[(LlvmBlock, [LlvmVar], [(LlvmVar, LlvmVar)])] -> Translator LlvmBlocks
-- propagatePhi l = do
--   let allUsed = map fst $ groupByFirst [(v,v) | v <- join $ map snd3 l]
--   propagateAll allUsed l
--   where propagateAll [] s = return $ map fst3 s
--         propagateAll (h:t) s = do
--           let mapped = map (\(b,u,a) -> (b, elem h u, fst <$> getFirst (\(_,v) -> v == h) a)) s
--           propd <- propagatePhiForVar h mapped
--           let mapL label = let (Just s) = getFirst (\b -> blockLabel b == label)  propd in s
--           propagateAll t $ map (\(b,v,a) -> (mapL (blockLabel b), v, a)) s


propagatePhiForVar::LlvmVar -> [(LlvmBlock, Bool, Maybe LlvmVar)] -> Translator LlvmBlocks
propagatePhiForVar v l = map fst3 <$> (modUntilOK v l)
  where modUntilOK v d = do
          let fNotOk = getFirst (snd3) d
          case fNotOk of
            Nothing -> return d
            Just (b,_,_) -> getForBlock v (blockLabel b) d >>= (modUntilOK v . snd)

getForBlock::LlvmVar -> Unique -> [(LlvmBlock, Bool, Maybe LlvmVar)] -> Translator (LlvmVar, [(LlvmBlock, Bool, Maybe LlvmVar)])
getForBlock v u c = do
  let successors = map (\(l, _, _) -> (blockLabel l, getSuccessors l)) c
  let predecessors = join $ map (\(u, l) -> map (,u) l) successors
  let preds = [p | (v,p) <- predecessors, v == u]
  let (b, r, rv) = getFirstSure (( == u) . blockLabel . fst3) c
  let createdVarType = getVarType $ pVarLower v
  if length preds == 1 then getFromBlock v (head preds) c
  else
    if isNothing rv then do
                          (rest, nv) <- if r then let (fp, sp, nv) = splitOnLoad v (blockStmts b) in return (fp ++ sp, nv)
                                        else (blockStmts b,) <$> newVar createdVarType
                          let ndd = (b, False, Just nv) : filter (( /= u) . blockLabel .fst3) c
                          (cv, nddd) <- foldl (\f n -> f >>= (\ (l, cc) -> (\ (a, b) -> (a : l, b)) <$> getFromBlock v n cc )) (return ([], ndd)) preds
                          let wo = filter (( /= u) . blockLabel .fst3) nddd
                          let phi = Assignment nv $ Phi createdVarType $ zipWith (\ v b -> (v, LMLocalVar b LMLabel)) cv preds
                          let fullBody = phi : rest
                          return (nv, (b {blockStmts = fullBody} , False, Just nv): wo)
    else do
           (cv, nddd) <- foldl (\f n -> f >>= (\ (l, cc) -> (\ (a, b) -> (a : l, b)) <$> getFromBlock v n cc )) (return ([], c)) preds
           let wo = filter (( /= u) . blockLabel .fst3) nddd
           (rest, nv) <- if r then let (fp, sp, nv) = splitOnLoad v (blockStmts b) in return (fp ++ sp, nv)
                         else (blockStmts b,) <$> newVar createdVarType
           let phi = Assignment nv $ Phi createdVarType $ zipWith (\ v b -> (v, LMLocalVar b LMLabel)) cv preds
           let fullBody = phi : rest
           return (nv, (b {blockStmts = fullBody} , False, rv): wo)


getFromBlock::LlvmVar -> Unique -> [(LlvmBlock, Bool, Maybe LlvmVar)] -> Translator (LlvmVar, [(LlvmBlock, Bool, Maybe LlvmVar)])
getFromBlock nv u c = do
  let (b, r, v) = getFirstSure (( == u) . blockLabel . fst3) c
  if isJust v then return (fromJust v,c)
  else do
         (recv, d) <- getForBlock nv u c
         let wo = filter (( /= u) . blockLabel .fst3) d
         return (recv, (b, r, Just recv): wo)


getSuccessors::LlvmBlock -> [Unique]
getSuccessors b =
  let lastStmt = last $ blockStmts b in
  case lastStmt of
    Return{} -> []
    Branch (LMLocalVar r _) -> [r]
    BranchIf _ (LMLocalVar r1 _) (LMLocalVar r2 _) -> [r1, r2]