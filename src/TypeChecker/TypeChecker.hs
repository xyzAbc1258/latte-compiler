{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}

module TypeChecker.TypeChecker where

import AbsLatte
import Control.Applicative(liftA2)
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State
import TypeChecker.TypeCheckCommon as TCC
import TypeChecker.TypeCheckUtils as TCC
import Data.Maybe
import Data.List
import Common.Utils
import Common.ASTUtils
import Common.ASTModifier as ASTM
import TypeChecker.TypeUtils
import qualified Data.Map as M
import qualified Common.Graphs as Gr
import Control.Lens((&))
import Data.Tuple(swap)
import TypeChecker.TypeCheckerStmts

checkTypes::(Positionable a) => Program a -> Either String (Program TCC.Type)
checkTypes p = evalPos $ runExceptT $ runReaderT (evalStateT (checkProgram p) 0)  baseStack

checkProgram::(Positionable a) => Program a -> TypeChecker (Program TCC.Type)
checkProgram (Program ppos defs) = do
    withPos ppos
    let classes = [c | c@ClDef{} <- defs]
    let inheritances = map (\(ClDef _ (Ident name) ext _) -> (name, case ext of
                                                                      NoExt{} -> []
                                                                      ClassExt _ (Ident c) -> [c])) classes

    unless (unique $ map fst inheritances) $ throwPosError "Class names must be unique"
    let inheritanceGraph = Gr.fromList inheritances
    when (Gr.hasCycle inheritanceGraph) $ mThrowError "Cycle in classes inheritance"
    let classesMap = M.fromList [(n,c) | c@(ClDef _ (Ident n) _ _) <- classes]
    let orderClasses = map (classesMap M.!) $ fromJust $ Gr.sortTopologically inheritanceGraph
    let funcs = [f | f@FnDef{} <- defs]
    let baseClassDecl = foldl (.) id [withClass n (createClassInfo n) |ClDef _ (Ident n) _ _ <- orderClasses]
    afterClassDecl <- local baseClassDecl $ foldl (\a b -> a >>=(\s -> local (const s) b)) ask $ map declare orderClasses
    afterFuncDecl <- foldl (\a b -> a >>=(\s -> local (const s) b)) (return afterClassDecl) $ map declare funcs
    decls <- local (const afterFuncDecl) $ checkTopDef defs
    --throwError ("e", afterFuncDecl)
    return $ ASTM.modifyI removeBlocks $ Program None decls

declare::(Positionable a) => TopDef a -> TypeChecker StackEnv
declare f@(FnDef pos rType (Ident name) args _) = do
  withPos pos
  exists <- existsFunction name Global
  when exists $ throwPosError $ "Function " ++ name ++ " was already defined"
  let argTypes = [t | Arg _ t _ <- args]
  let allTypes = map mapType (rType : argTypes)
  inErrorContext name $ mapM_ typeExists allTypes
  let funcInfo = toFuncDef f
  asks (withFunction name funcInfo)

declare (ClDef pos (Ident name) ext members) = do
  withPos pos
  exists <- existsClass name Global
  let sameNameAsPrim = name `elem` map show primitives
  when sameNameAsPrim $ throwPosError $ "Type " ++ name ++ " was already declared."
  baseClass <- case ext of
    NoExt{} -> return $ createClassInfo name
    ClassExt pos (Ident bClass) -> do
                              existsBaseClass <- existsClass bClass Global
                              unless existsBaseClass $ throwPosError $ "Type " ++ bClass ++ " doesnt exists"
                              bInfo <- fromJust <$> getInScope Global (classI bClass)
                              return $ bInfo {_baseClass = Just bClass, _name = name}
  declareNew <- foldl (>>=) (return baseClass) $ map addDeclaration members
  asks (withClass name declareNew)
  where addDeclaration (ClFld pos t (Ident name)) ci = do
                                                      when (M.member name $ _components ci) $ throwPosError $ "Member " ++ name ++ " was already declared"
                                                      let nt = mapType t
                                                      typeExists nt
                                                      return $ addVariable name nt ci
        addDeclaration (ClFunc _ rType (Ident fName) args _) ci = do
                                                                   let existing = _components ci M.!? fName
                                                                   let resFType = TCC.Fun (mapType rType) (map mapType [t | Arg _ t _ <- args] )
                                                                   when (isJust existing && existing /= Just resFType) $ mThrowError $ "Member " ++ fName ++ " was already declared with different type!"
                                                                   return $ addFunction fName resFType ci

checkTopDef::(Positionable a) => [TopDef a] -> TypeChecker [TopDef TCC.Type]
checkTopDef (f@(FnDef _ rType (Ident name) args block): rest) = do
  td <- inErrorContext name $ checkFnDef f
  (td ++) <$> checkTopDef rest


checkTopDef (ClDef _ (Ident name) exts decls : rest) = do
  ci <- fromJust <$> getInScope Global (classI name)
  let fNameMap fName = _fMapping (_vtable ci) M.! (_fNameMapping (_vtable ci) M.! fName) & fst
  let fndefs = [FnDef w r (Ident $ fNameMap n) (Arg w (AbsLatte.Class w (Ident name)) (Ident thisName): a) b | (ClFunc w r (Ident n) a b) <- decls]
  let structTypes = _varNameMapping ci & M.toList & map swap & sortOn fst & map snd & map (_components ci M.!) & map mapTypeBack
  let structDef = Struct TCC.None (Ident name) $ map (None <$) structTypes
  let classVTable = _vtable ci
  let fMapping = _fMapping classVTable
  let comps = _components ci
  let funcsDecls = classVTable & _fNameMapping & M.toList & sortOn snd & map (\s -> (fMapping M.! snd s,comps M.! fst s)) & map toFuncDelc
  let vtable = VirtArray None (Ident ("virt_" ++ name)) $ map (None <$) funcsDecls
  r <- local (createEnvFromClassInfo ci :) $ checkTopDef fndefs
  ((structDef : vtable : r) ++) <$> checkTopDef rest
  where toFuncDelc ((fname, cName), TCC.Fun ret args) = FuncDecl () (mapTypeBack ret) (Ident fname) (map mapTypeBack (TCC.Class cName : args))

checkTopDef [] = do
  mainF <- getInScope Global $ functionI "main"
  when (isNothing mainF) $ mThrowError "Function main is not defined"
  let (FunctionInfo _ rType args) = fromJust mainF
  unless (rType == TCC.Int) $ mThrowError "Main has to return int"
  unless (null args) $ mThrowError "Main cannot have any arguments"
  return []

checkFnDef::(Positionable a) => TopDef a -> TypeChecker [TopDef TCC.Type]
  --TODO refactor...
checkFnDef (FnDef pos rType (Ident name) args block@(Block _ stmts)) = do
  withPos pos
  let argTypes = [t | Arg _ t _ <- args]
  let allTypes = map mapType (rType : argTypes)
  when (TCC.Void `elem` tail allTypes) $ throwPosError "Function argument cannot have type void"
  let varNames = retVarName : [n | Arg _ _ (Ident n) <- args]
  unless (unique varNames) $ throwPosError "Argument names are not unique"
  nArgs <- mapM (\(Arg a t _) -> Arg a t . Ident <$> newIdentifier) args
  let variablesModifier = foldl1 (.) $ zipWith withVariable varNames allTypes
  let decls = [Decl None (None <$ t) [Init nt id (EVar nt nName)] |((Arg a t id, Arg _ _ nName), nt) <- zip (zip args nArgs) (tail allTypes) ]
  blockE <- local variablesModifier $ checkBlock block
  let (Block n s) = blockE
  let nBlock = Block n (decls ++ s)
  unless (checkHasReturn (head allTypes == TCC.Void) s) $ throwPosError "There is a branch without return statement"
  return [FnDef TCC.None (None <$ rType) (Ident name) (zipWith (<$) (tail allTypes) nArgs) nBlock]



