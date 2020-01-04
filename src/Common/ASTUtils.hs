{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module Common.ASTUtils where

import AbsLatte


extractS::Stmt a -> a
extractS x = case x of
                     Empty a -> a
                     BStmt a block -> a
                     NamedBStmt a ident block -> a
                     Decl a type_ items -> a
                     Ass a expr1 expr2 -> a
                     Incr a expr -> a
                     Decr a expr -> a
                     Ret a expr -> a
                     VRet a -> a
                     Cond a expr stmt -> a
                     CondElse a expr stmt1 stmt2 -> a
                     While a expr stmt -> a
                     For a type_ ident expr stmt -> a
                     SExp a expr -> a
                     CondJump a expr ident1 ident2 -> a
                     Jump a ident -> a

extract::Expr t -> t
extract (EVar a _) = a
extract (ELitInt a _) = a
extract (ELitTrue a) = a
extract (ELitFalse a) = a
extract (EFldAcc a _ _) = a
extract (EArrAcc a  _ _) = a
extract (ENewObj a _) = a
extract (ENewArr a _ _) = a
extract (EApp a _ _) = a
extract (EString a _) = a
extract (Neg a _) = a
extract (Not a _) = a
extract (EMul a _ _ _) = a
extract (EAdd a _ _ _) = a
extract (ERel a _ _ _) = a
extract (EAnd a _ _) = a
extract (EOr a _ _) = a
extract (EFldNoAcc a _ _) = a
extract (EVirtCall a _ _ _)= a
extract (ENull a _) = a

class IntOp a r | a -> r where
  op::a -> Integer -> Integer -> r

instance IntOp (AddOp a) Integer where
  op Plus{} = (+)
  op Minus{} = (-)

instance IntOp (MulOp a) Integer where
  op Times{} = (*)
  op Div{} = div
  op Mod{} = mod

instance IntOp (RelOp a) Bool where
  op LTH {} = (<)
  op LE{} = (<=)
  op GTH {} = (>)
  op GE{} = (>=)
  op EQU {} = (==)
  op NE{} = (/=)

boolExpr::a -> Bool -> Expr a
boolExpr a True = ELitTrue a
boolExpr a False = ELitFalse a

fromBoolExpr::Expr a -> Bool
fromBoolExpr ELitFalse{} = False
fromBoolExpr ELitTrue{} = True

isSimpleBoolExpr::Expr a -> Bool
isSimpleBoolExpr ELitTrue{} = True
isSimpleBoolExpr ELitFalse{} = True
isSimpleBoolExpr _ = False

isTrueExpr::Expr a -> Bool
isTrueExpr ELitTrue{} = True
isTrueExpr _ = False

isFalseExpr::Expr a -> Bool
isFalseExpr ELitFalse{} = True
isFalseExpr _ = False

removeBlocks::[Stmt a] -> [Stmt a]
removeBlocks [] = []
removeBlocks (BStmt _ (Block _ b) : r) = removeBlocks b ++ removeBlocks r
removeBlocks (Cond a e b : r) = Cond a e (rmBlocksExcFirst b) : removeBlocks r
removeBlocks (CondElse a e t f : r) = CondElse a e (rmBlocksExcFirst t) (rmBlocksExcFirst f) : removeBlocks r
removeBlocks (While a e b : r) = While a e (rmBlocksExcFirst b) : removeBlocks r
removeBlocks (t : r) = t : removeBlocks r

rmBlocksExcFirst::Stmt a -> Stmt a
rmBlocksExcFirst (BStmt bsa (Block ba b)) = let nb = removeBlocks b in BStmt bsa (Block ba nb)
rmBlocksExcFirst a = let [na] = removeBlocks [a] in na

checkHasReturn::Bool -> [Stmt a] -> Bool
checkHasReturn isVoid [] = isVoid
checkHasReturn isVoid (BStmt _ (Block _ b): r) = checkHasReturn isVoid (b ++ r)
checkHasReturn _ (Ret{}:_) = True -- sprawdzanie typów jest gdzieś indziej
checkHasReturn _ (VRet{} : _) = True
checkHasReturn isVoid [Cond _ _ s] = isVoid
checkHasReturn isVoid (CondElse _ _ ifT ifF :r) = (checkHasReturn isVoid [ifT] && checkHasReturn isVoid [ifF]) || checkHasReturn isVoid r
checkHasReturn isVoid (While _ ELitTrue{} _ : r) = True -- nieskończone pętle jeśli się zakończą, to returnem ze środka, a jak nie to nie nasz problem
checkHasReturn isVoid [While _ _ b] = checkHasReturn isVoid [b]
checkHasReturn isVoid [For _ _ _ _ b] = checkHasReturn isVoid [b]
checkHasReturn isVoid (_:r) = checkHasReturn isVoid r


isEmptyStmt :: Stmt a -> Bool
isEmptyStmt Empty{} = True
isEmptyStmt (BStmt _ (Block _ l)) = all isEmptyStmt l
isEmptyStmt _ = False

-- Najbardziej podstawowa wersja sprawdzania efektów ubocznych
isPure::Expr a -> Bool
isPure EString{} = True
isPure EVar{} = True
isPure ELitInt{} = True
isPure ELitTrue{} = True
isPure ELitFalse{} = True
isPure (ERel _ e1 _ e2) = isPure e1 && isPure e2
isPure (EAdd _ e1 _ e2) = isPure e1 && isPure e2
isPure (EMul _ e1 _ e2) = isPure e1 && isPure e2
isPure EVirtCall{} = False
isPure EApp{} = False
isPure EFldNoAcc{} = False
isPure EFldAcc{} = False
isPure EArrAcc{} = False
isPure (EAnd _ e1 e2) = isPure e1 && isPure e2
isPure (EOr _ e1 e2) = isPure e1 && isPure e2
isPure ENull{} = True
isPure ENewObj{} = False
isPure ENewArr{} = False
isPure (Neg _ e) = isPure e
isPure (Not _ e) = isPure e
isPure _ = False -- jakbym coś pominął