module Compiler.BlockGenerator where

import AbsLatte
import TypeChecker.TypeCheckUtils as TCC
import Control.Monad.State
import Common.Utils
import Common.ASTUtils
import qualified Common.ASTModifier as ASTM

type LabelGen = State Int

genLabel:: LabelGen Ident
genLabel = do
  c <- get
  modify (1 +)
  return $ Ident $ "label_" ++ (show c)

toBlockStructure::(Defaultable a) => Program a -> Program a
toBlockStructure = (`evalState` 0) . ASTM.modify splitStmtsToBlocksA

controls::Stmt a -> Bool
controls Cond{} = True
controls CondElse {} = True
controls While {} = True
controls _ = False

lastLabel = Ident "last"

splitStmtsToBlocksA::(Defaultable a) =>[Stmt a] -> LabelGen [Stmt a]
splitStmtsToBlocksA s = do
  let first = Ident "entry"
  splitStmtsToBlocks first s lastLabel

splitStmtsToBlocks::(Defaultable a) =>Ident -> [Stmt a] -> Ident -> LabelGen [Stmt a]
splitStmtsToBlocks current s next = do
  let splitted = splitOn controls s
  mapBlocks current splitted next

mapBlocks::(Defaultable a) =>Ident -> [[Stmt a]] -> Ident -> LabelGen[Stmt a]
mapBlocks c [] _ = return [VRet getDefault]
mapBlocks c [h] n = processBlock c h n
mapBlocks c (h:t) n = do
  nextLabel <- genLabel
  b <- processBlock c h nextLabel
  (b ++) <$> mapBlocks nextLabel t n

processBlock::(Defaultable a) =>Ident -> [Stmt a] -> Ident -> LabelGen [Stmt a]
processBlock current [Cond a cond (BStmt _ (Block ba ifT))] next = do
  iftLabel <- genLabel
  condBlock <- genCondBlocks current cond iftLabel next
  blocks <- splitStmtsToBlocks iftLabel ifT next
  return $ condBlock ++ blocks

processBlock current [Cond a cond b] next = processBlock current [Cond a cond (BStmt a (Block a [b]))] next

processBlock current [CondElse a cond (BStmt _ (Block bat ifT)) (BStmt _ (Block baf ifF))] next = do
  iftLabel <- genLabel
  iffLabel <- genLabel
  condBlock <- genCondBlocks current cond iftLabel iffLabel
  tBlocks <- splitStmtsToBlocks iftLabel ifT next
  fBlocks <- splitStmtsToBlocks iffLabel ifF next
  return $ condBlock ++ (tBlocks ++ fBlocks)

processBlock current [CondElse a cond ift (BStmt _ (Block baf ifF))] next =
  processBlock current [CondElse a cond (BStmt a (Block baf [ift])) (BStmt a (Block baf ifF))] next

processBlock current [CondElse a cond (BStmt _ (Block baf ift)) iff] next =
  processBlock current [CondElse a cond (BStmt a (Block baf ift)) (BStmt a (Block baf [iff]))] next

processBlock current [CondElse a cond ift iff] next =
  processBlock current [CondElse a cond (BStmt a (Block a [ift])) (BStmt a (Block a [iff]))] next

processBlock current [While a cond (BStmt _ (Block bat ifT))] next = do
  whileLabel <- genLabel
  condBlock <- genCondBlocks current cond whileLabel next
  whileBlocks <- splitStmtsToBlocks whileLabel ifT current
  return $ whileBlocks ++ condBlock

processBlock current [While a cond ift] next =
  processBlock current [While a cond (BStmt a (Block a [ift]))] next

processBlock current b next = do
  let lastStmt = last b
  let v = extractS lastStmt
  let s = case lastStmt of
              VRet{} -> NamedBStmt v current (Block v b)
              Ret{} -> NamedBStmt v current (Block v b)
              -- na końcy bloku gdy nie ma "sensownego" następnika, robimy return
              s | next == lastLabel -> NamedBStmt v current (Block v $ b ++ [AbsLatte.VRet v])  
              s -> NamedBStmt v current (Block v $ b ++ [AbsLatte.Jump v next])
  return [s]

genCondBlocks::(Defaultable a) => Ident -> Expr a -> Ident -> Ident -> LabelGen [Stmt a]
genCondBlocks c (EAnd _ v1 v2) t f = do
  mid <- genLabel
  first <- genCondBlocks c v1 mid f
  sec <- genCondBlocks mid v2 t f
  return $ first ++ sec

genCondBlocks c (EOr _ v1 v2) t f = do
  mid <- genLabel
  first <- genCondBlocks c v1 t mid
  sec <- genCondBlocks mid v2 t f
  return $ first ++ sec

genCondBlocks c (Not _ e) t f = genCondBlocks c e f t

genCondBlocks c e t f = let d = getDefault in return [NamedBStmt d c (Block d [AbsLatte.CondJump d e t f])]