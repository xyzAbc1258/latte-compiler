module Compiler.BlockGenerator where

import AbsLatte
import TypeChecker.TypeCheckUtils as TCC
import Control.Monad.State as S
import Common.Utils
import Common.ASTUtils
import qualified Common.ASTModifier as ASTM
import Common.Graphs as G
import qualified Data.Set as Set
import qualified Data.Map as M
import Data.List as List
import Data.Tuple
import Compiler.BaseExprFormTransformer
import Control.Monad.Writer (runWriterT)

type LabelGen = State Integer

genLabel:: LabelGen Ident
genLabel = do
  c <- get
  S.modify (1 +)
  return $ Ident $ "label_" ++ show c


toBlockStructure::Program TCC.Type -> Program TCC.Type
toBlockStructure = (`evalState` 0) . ASTM.modify splitStmtsToBlocksA

controls::Stmt TCC.Type -> Bool
controls Cond{} = True
controls CondElse {} = True
controls While {} = True
controls _ = False

lastLabel = Ident "last"
first = Ident "entry"

entryBlock next = NamedBStmt None first (Block None [Jump None next])

splitStmtsToBlocksA::[Stmt TCC.Type] -> LabelGen [Stmt TCC.Type]
splitStmtsToBlocksA s = do
  next <- genLabel
  stmts <- (entryBlock next :) <$> splitStmtsToBlocks next s lastLabel
  if length stmts  < 2 then return stmts
  else return $ entryFirst $ compactBlocks stmts

entryFirst::[Stmt TCC.Type] -> [Stmt TCC.Type]
entryFirst s =
  let [entry] = [n | n@(NamedBStmt _ (Ident name) _ ) <- s, name == "entry"] in
  let rest = [n | n@(NamedBStmt _ (Ident name) _ ) <- s, name /= "entry"] in
  entry : rest

compactBlocks::[Stmt TCC.Type] -> [Stmt TCC.Type]
compactBlocks s =
  let successors = flatMap successor s in
  let succMap = M.fromList $ groupByFirst successors in
  let predMap = M.fromList $ groupByFirst (map swap successors) in
  let withSingleSucc = M.map head $ M.filter (( == 1) . length) succMap in
  let withSinglePred = M.map head $ M.filter (( == 1) . length) predMap in
  let toCompact = M.filterWithKey (\ k v -> (withSinglePred M.!? v) == Just k) withSingleSucc in
  if M.null toCompact then s
  else
    let (n, h) = head $ M.toList toCompact in
    let (Just ind) = List.findIndex (\(NamedBStmt _ na _) -> na == n) s in
    let (NamedBStmt _ _ (Block _ hb), NamedBStmt v nn (Block vb hs)) = (findByName h s, findByName n s) in
    let rest = filter (\(NamedBStmt _ r _) -> r /= n && r /= h) s in
    let nBlock = NamedBStmt v n (Block vb $ init hs ++ hb) in
    let (f,r) = List.splitAt ind rest in
    compactBlocks (f ++ [nBlock] ++ r) -- pojedynczo żeby nie napsuć :)


findByName id sts =
  case filter (\(NamedBStmt _ n _) -> n == id) sts of
    [r] -> r
    l -> error $ show l ++ " $ " ++ show id ++ " $ " ++ show sts


successor::Stmt TCC.Type -> [(Ident,Ident)]
successor (NamedBStmt _ _ (Block _ [])) = []
successor (NamedBStmt _ n (Block _ s)) =
  let l = last s in
  case l of
    VRet {} -> []
    Ret {} -> []
    CondJump _ _ r1 r2 -> [(n,r1),(n,r2)]
    Jump _ r -> [(n,r)]
successor s = error $ "successor " ++ show s

splitStmtsToBlocks::Ident -> [Stmt TCC.Type] -> Ident -> LabelGen [Stmt TCC.Type]
splitStmtsToBlocks current s next = do
  let splitted = splitOn controls s
  mapBlocks current splitted next

mapBlocks::Ident -> [[Stmt TCC.Type]] -> Ident -> LabelGen[Stmt TCC.Type]
mapBlocks c [] _ = return [NamedBStmt None c (Block None [VRet getDefault])]
mapBlocks c [h] n = processBlock c h n
mapBlocks c (h:t) n = do
  nextLabel <- genLabel
  b <- processBlock c h nextLabel
  (b ++) <$> mapBlocks nextLabel t n

processBlock::Ident -> [Stmt TCC.Type] -> Ident -> LabelGen [Stmt TCC.Type]
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

genCondBlocks::Ident -> Expr TCC.Type -> Ident -> Ident -> LabelGen [Stmt TCC.Type]
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

genCondBlocks c e t f = do
  (ne, s) <- runWriterT $ toBaseExpr e
  let d = getDefault
  case s of 
    [] -> return [NamedBStmt d c (Block d [AbsLatte.CondJump d e t f])]
    _ -> do 
           n <- genLabel
           nst <- splitStmtsToBlocks c s n
           return $ nst ++ [NamedBStmt d n (Block d [AbsLatte.CondJump d ne t f])]