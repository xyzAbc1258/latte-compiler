{-# LANGUAGE TupleSections #-}
module Compiler.ILTranformer where

import Llvm
import AbsLatte as A
import TypeChecker.TypeCheckUtils as TCU
import FastString (mkFastString)
import Outputable (showSDocUnsafe, SDoc)
import Control.Monad.State
import qualified Data.Map as M
import Unique (getUnique)
import Control.Lens
import Common.ASTUtils
import qualified TypeChecker.TypeCheckCommon as TCC
import Compiler.ILTransformerCommon
import Compiler.ILBlockTransformer
import Data.Char (showLitChar)
import Common.Utils

toString:: Program TCU.Type -> String
toString = showSDocUnsafe .  ppLlvmModule . (`evalState` (M.empty,0)) . transformProgram

toDoc:: Program TCU.Type -> SDoc
toDoc = ppLlvmModule . (`evalState` (M.empty,0)) . transformProgram

transformProgram::Program TCU.Type -> Translator LlvmModule
transformProgram (Program a topdefs) = do
  -- TODO better
 let dec = map ((\(FunctionInfo n r a) ->  FnDef () (mapTypeBack r) (Ident n) (map ((\t -> Arg () t (Ident "s") ) . mapTypeBack) a) (Block ()[])). snd) (M.toList $ _functions $ head TCC.baseStack)
 mapM_ declareFunc (map (None <$) dec)
 let aliases = [transformAlias s | s@Struct{} <- topdefs]
 varrays <- mapM transformVirtArray [v | v@VirtArray{} <- topdefs]
 mapM_ declareFunc [f | f@FnDef{} <- topdefs]
 funcs <- mapM translateFunction [f | f@FnDef{} <- topdefs]
 ss <- M.toList . fst <$> get
 let sConsts = [LMGlobal v (Just $ LMStaticStr (mkfs $ replace "\\n" "\\0A" $ foldl (.) id (map showLitChar text) []) (LMArray (length text +1) i8)) | (_:_:_:_:_:text,v@LMGlobalVar{}) <- ss, getLink v == Private]
 return $ LlvmModule {
  modComments = [],
  modAliases = aliases,
  modMeta = [],
  modGlobals = varrays ++ sConsts,
  modFwdDecls = [],
  modFuncs = funcs
}


transformAlias::TopDef TCU.Type -> LlvmAlias
transformAlias (Struct _ (Ident name) types) = (mkFastString name, LMStructU $ (LMPointer i8Ptr :) $ map valType types)

declareFunc::TopDef TCU.Type -> Translator ()
declareFunc (FnDef _ rt (Ident fName) args body) = do
  let var = LMGlobalVar (mkFastString fName)
                           (LMFunction
                              LlvmFunctionDecl{decName = mkFastString fName,
                                               funcLinkage = Internal, funcCc = CC_Fastcc,
                                               decReturnType = valType rt,
                                               decVarargs = FixedArgs,
                                               decParams = map (\ s -> (valType s, [])) [t | Arg _ t _ <- args],
                                               funcAlign = Nothing})
                              Internal
                              Nothing
                              Nothing
                              Constant
  addVar fName var

transformVirtArray::TopDef TCU.Type -> Translator LMGlobal
transformVirtArray (VirtArray _ (Ident name) funcDecls) = do
  let gvar = LMGlobalVar
                        (mkFastString name)
                        (LMArray (length funcDecls) i8Ptr)
                        Internal
                        Nothing
                        Nothing
                        Constant
  addVar name gvar
  fDecls <- mapM funcDeclToStatic funcDecls
  return $LMGlobal {
    getGlobalVar = gvar,
    getGlobalValue = Just (
      LMStaticArray
        ( map (`LMBitc` i8Ptr) fDecls)
        (LMArray (length funcDecls) i8Ptr)
    )
  }

funcDeclToStatic::FuncDec TCU.Type -> Translator LlvmStatic
funcDeclToStatic (FuncDecl _ r (Ident name) args) = do let funcDecl
                                                             = LlvmFunctionDecl{decName = mkFastString name,
                                                                                funcLinkage = Internal, funcCc = CC_Fastcc,
                                                                                decReturnType = valType r, decVarargs = FixedArgs,
                                                                                decParams = map (\ s -> (valType s, [])) args,
                                                                                funcAlign = Nothing}
                                                       let func
                                                             = LMGlobalVar (mkFastString name) (LMPointer $ LMFunction funcDecl)
                                                                 Internal
                                                                 Nothing
                                                                 Nothing
                                                                 Constant
                                                       addVar name func
                                                       return $ LMStaticPointer func


translateFunction::TopDef TCU.Type -> Translator LlvmFunction
translateFunction (FnDef _ _ (Ident fname) args (Block _ body)) = do
  varDef <- getVar fname
  let (LMGlobalVar _ (LMFunction decl) _ _ _ _ ) = varDef
  let funcArgs = [mkfs n | Arg _ _ (Ident n) <- args]
  mapM_ (uncurry addVar) [(n, LMNLocalVar (mkfs n) $ valType t) | Arg _ t (Ident n) <- args]
  blocks <- transformBody body
  return $ LlvmFunction {
    funcDecl = decl,
    funcArgs = funcArgs,
    funcAttrs = [],
    funcSect = Nothing,
    funcPrefix =  Nothing,
    funcBody = blocks
  }


