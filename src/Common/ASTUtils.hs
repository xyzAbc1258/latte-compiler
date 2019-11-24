module Common.ASTUtils where

import AbsLatte


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
extract (ENull a) = a
extract (ECast a _ _) = a