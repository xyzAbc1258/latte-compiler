module Compiler.ILTranformer where

import MyLlvm.Llvm
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
import GHC.Show (showLitString)
import Common.Utils
import Compiler.LlvmSimplifier
import Debug.Trace (trace)

toString:: Program TCU.Type -> String
toString = showSDocUnsafe .  ppLlvmModule . (`evalState` (M.empty,0)) . transformProgram

toDoc:: Program TCU.Type -> SDoc
toDoc = ppLlvmModule . (`evalState` (M.empty,0)) . transformProgram


transformProgram::Program TCU.Type -> Translator LlvmModule
transformProgram (Program a topdefs) = do
  stdFuncs <- declareStandardFunctions
  let aliases = [transformAlias s | s@Struct{} <- topdefs]
  varrays <- mapM transformVirtArray [v | v@VirtArray{} <- topdefs]
  mapM_ declareFunc [f | f@FnDef{} <- topdefs]
  funcs <- mapM translateFunction [f | f@FnDef{} <- topdefs]
  ss <- gets (M.toList . fst)
  -- dziwny brak obsługi nowych linii :/
  let sConsts = [LMGlobal v (Just $ LMStaticStr (mkfs conv) (LMArray (sLength conv +1) i8))
                    | (_:_:_:_:_:text,v@LMGlobalVar{}) <- ss, getLink v == Private, let conv = convertString text]
  return $ LlvmModule {
    modComments = [],
    modAliases = aliases,
    modMeta = [],
    modGlobals = varrays ++ sConsts,
    modFwdDecls = stdFuncs,
    modFuncs = funcs
  } 

declareStandardFunctions::Translator LlvmFunctionDecls
declareStandardFunctions = do
  let stdLib = fmap snd $ M.toList $ _functions $ head TCC.baseStack
  let mtb = mapTypeBack
  let createDummyArg argType = Arg () argType (Ident "dummyName")
  let emptyBlock = Block ()[]
  let createFuncDecl rType name = FnDef () rType (Ident name)
  let createFuncDeclFromTCUTypes r n a = createFuncDecl (mtb r) n (map (createDummyArg . mtb) a) emptyBlock
  let declarations = map (\ (FunctionInfo n r a) -> createFuncDeclFromTCUTypes r n a) stdLib
  mapM (declareFunc . (None <$)) declarations

transformAlias::TopDef TCU.Type -> LlvmAlias
transformAlias (Struct _ (Ident name) types) = (mkFastString name, LMStruct $ (LMPointer i8Ptr :) $ map valType types)

declareFunc::TopDef TCU.Type -> Translator LlvmFunctionDecl
declareFunc (FnDef _ rt (Ident fName) args body) = do
  let decl = LlvmFunctionDecl{decName = mkFastString fName,
                                                            funcLinkage = ExternallyVisible, funcCc = CC_Ccc,
                                                            decReturnType = valType rt,
                                                            decVarargs = FixedArgs,
                                                            decParams = map (\ s -> (valType s, [])) [t | Arg _ t _ <- args],
                                                            funcAlign = Nothing}

  let var = LMGlobalVar (mkFastString fName)
                           (LMFunction
                              decl)
                              ExternallyVisible
                              Nothing
                              Nothing
                              Constant
  addVar fName var
  return decl

transformVirtArray::TopDef TCU.Type -> Translator LMGlobal
transformVirtArray (VirtArray _ (Ident name) funcDecls) = do
  let gvar = LMGlobalVar
                        (mkFastString name)
                        (LMArray (length funcDecls) i8Ptr)
                        ExternallyVisible
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
                                                                                funcLinkage = ExternallyVisible, funcCc = CC_Ccc,
                                                                                decReturnType = valType r, decVarargs = FixedArgs,
                                                                                decParams = map (\ s -> (valType s, [])) args,
                                                                                funcAlign = Nothing}
                                                       let func
                                                             = LMGlobalVar (mkFastString name) (LMPointer $ LMFunction funcDecl)
                                                                 ExternallyVisible
                                                                 Nothing
                                                                 Nothing
                                                                 Constant
                                                       --addVar name func
                                                       return $ LMStaticPointer func


translateFunction::TopDef TCU.Type -> Translator LlvmFunction
translateFunction (FnDef _ _ (Ident fname) args (Block _ body)) = do
  varDef <- getVar fname
  nState <- gets fst
  let (LMGlobalVar _ (LMFunction decl) _ _ _ _ ) = varDef
  let funcArgs = [mkfs n | Arg _ _ (Ident n) <- args]
  mapM_ (uncurry addVar) [(n, LMNLocalVar (mkfs n) $ valType t) | Arg _ t (Ident n) <- args]
  blocks <- transformFuncBody body
  let function =  tailCallOptimization $ LlvmFunction {
    funcDecl = decl,
    funcArgs = funcArgs,
    funcAttrs = [],
    funcSect = Nothing,
    funcPrefix =  Nothing,
    funcBody = blocks
  }
  current <- gets fst
  let globals = M.fromList [(k,v) | (k,v@LMGlobalVar{}) <- M.toList current]
  modify (_1 %~ const (M.union nState globals))
  return function

