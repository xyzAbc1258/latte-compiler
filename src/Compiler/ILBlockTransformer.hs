module Compiler.ILBlockTransformer where

import Llvm
import AbsLatte as A
import TypeChecker.TypeCheckUtils as TCU
import Compiler.ILTransformerCommon
import Compiler.ILStmtTransformer
import Unique (getUnique)
import Control.Monad.Writer

transformBody::[Stmt TCU.Type] -> Translator LlvmBlocks
transformBody s = do
  let labels = [(n, LMLocalVar (getUnique $ mkfs n) LMLabel) | NamedBStmt _ (Ident n) _ <- s ]
  mapM_ (uncurry addVar) labels
  mapM transformBlock s

transformBlock::Stmt TCU.Type -> Translator LlvmBlock
transformBlock (NamedBStmt _ (Ident name) (Block _ stmts)) = do
    vLabel <- getVar name
    let (LMLocalVar label _) = vLabel
    lmStmts <- execWriterT $ mapM_ transformStmt stmts
    return $ LlvmBlock {
      blockLabel = label,
      blockStmts = lmStmts
    }

transformBlock A.Empty{} = return $ LlvmBlock {
                                 blockLabel = getUnique $ mkfs "entry",
                                 blockStmts = [Return Nothing]
                               }


transformBlock A.VRet {} = return $ LlvmBlock {
                                       blockLabel = getUnique $ mkfs "entry",
                                       blockStmts = [Return Nothing]
                                 }
transformBlock t = error $ "Incorrect block " ++ show t