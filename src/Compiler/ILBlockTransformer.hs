module Compiler.ILBlockTransformer where

import MyLlvm.Llvm
import AbsLatte as A
import TypeChecker.TypeCheckUtils as TCU
import Compiler.ILTransformerCommon
import Compiler.ILStmtTransformer
import Unique (getUnique)
import Control.Monad.Writer
import qualified Data.Map as M
import Compiler.PhiPropagator
import Compiler.LlvmSimplifier

transformFuncBody::[Stmt TCU.Type] -> Translator LlvmBlocks
transformFuncBody s = do
  blocks <- transformBody s
  simplifyLlvm <$> propagatePhi blocks

transformBody::[Stmt TCU.Type] -> Translator [(LlvmBlock,[LlvmVar], [(LlvmVar, LlvmVar)])]
transformBody s = do
  let labels = [(n, LMLocalVar (getUnique $ mkfs n) LMLabel) | NamedBStmt _ (Ident n) _ <- s ]
  mapM_ (uncurry addVar) labels
  mapM transformBlock s

transformBlock::Stmt TCU.Type -> Translator (LlvmBlock, [LlvmVar], [(LlvmVar, LlvmVar)])
transformBlock (NamedBStmt _ (Ident name) (Block _ stmts)) = do
    vLabel <- getVar name
    let (LMLocalVar label _) = vLabel
    (lmStmts, (locals,_)) <- flip runLocal (M.empty, []) $ execWriterT $ mapM_ transformStmt stmts 
    usedVariables <- mapM getVar $ M.keys $ M.filter (varReads .snd) locals 
    let toSave = map (\(n, (v, _)) -> (n, v)) $ filter (varWrites . snd . snd) $ M.toList locals
    stores <-  mapM (\(n, v) -> Store v <$> getVar n) toSave
    let finalVals = map (\(Store f v) -> (v,f)) stores
    let (ret: blockS) = reverse lmStmts
    let fBlock = case ret of
                Return{} ->  LlvmBlock {
                                blockLabel = label,
                                blockStmts = lmStmts
                              }
                _ -> LlvmBlock {
                                 blockLabel = label,
                                 blockStmts = reverse blockS ++ [ret] --reverse blockS ++ stores ++ [ret] -- ssa to załatwia
                               }
    return (fBlock,usedVariables, finalVals)

transformBlock A.Empty{} = return (LlvmBlock {
                                 blockLabel = getUnique $ mkfs "entry",
                                 blockStmts = [Return Nothing]
                               }, [], [])


transformBlock A.VRet {} = return (LlvmBlock {
                                       blockLabel = getUnique $ mkfs "entry",
                                       blockStmts = [Return Nothing]
                                 },[],[])
                                 
transformBlock t = error $ "Incorrect block " ++ show t