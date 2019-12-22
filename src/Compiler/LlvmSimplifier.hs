module Compiler.LlvmSimplifier where

import Llvm
import Compiler.ILTransformerCommon
import Data.List
import Common.Utils

simplifyLlvm::LlvmBlocks -> LlvmBlocks
simplifyLlvm = simplifyConstants . removeSingleValuePhis

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

