module Compiler.PhiSimplifier where

import Llvm
import Compiler.ILTransformerCommon
import Data.List

simplifyLlvm::LlvmBlocks -> LlvmBlocks
simplifyLlvm = removeSingleValuePhis

-- przy przekształcaniu do ssa potrafią powstać %v = phi [%v, %1], [%c, %3] więc podmieniamy %v na %c 
removeSingleValuePhis::LlvmBlocks -> LlvmBlocks
removeSingleValuePhis bs =
  let allStmts = join $ map blockStmts bs in
  let stmtsToRemove = [a | a@(Assignment r (Phi _ v)) <- allStmts, length (nub $ filter (/= r) $ fst <$> v) == 1] in
  if null stmtsToRemove then bs
  else -- usuwamy pojedynczo żeby niczego nie napsuć, wszystko na raz potrafi napsuć niestety :)
    let currentRm@(Assignment r (Phi _ v)) = head stmtsToRemove in
    let toReplace = head $ nub $ filter (/= r) $ fst <$> v in
    let newBs = map (\b -> b { blockStmts = filter (/= currentRm) $ blockStmts b}) bs in
    let finalBs = map (replaceVars r toReplace) newBs in
    removeSingleValuePhis finalBs


