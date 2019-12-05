module Compiler.ILBlockTransformer where

import Llvm
import AbsLatte as A
import TypeChecker.TypeCheckUtils as TCU
import Compiler.ILTransformerCommon
import Compiler.ILStmtTransformer
import Unique (getUnique)

transformBody::[Stmt TCU.Type] -> Translator LlvmBlocks
transformBody = mapM transformBlock

transformBlock::Stmt TCU.Type -> Translator LlvmBlock
transformBlock (NamedBStmt _ (Ident name) (Block _ stmts)) = do
    lmStmts <- mapM transformStmt stmts
    let label = getUnique $ mkfs name
    return $ LlvmBlock {
      blockLabel = label,
      blockStmts = join lmStmts
    }

transformBlock A.Empty{} = return $ LlvmBlock {
                                 blockLabel = getUnique $ mkfs "entry",
                                 blockStmts = [Return Nothing]
                               }


transformBlock b = error $ "Incorrect block! " ++ show b
