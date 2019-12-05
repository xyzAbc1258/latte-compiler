{-# LANGUAGE FlexibleContexts #-}

module TypeChecker.ExprSimplification where

import AbsLatte
import TypeChecker.TypeCheckUtils (MonadRErrorC, mThrowError)
import Common.ASTUtils (isSimpleBoolExpr, boolExpr, fromBoolExpr, op)

simplifyExpr::(MonadRErrorC String m) => Expr a -> m (Expr a)
simplifyExpr (Neg t (ELitInt _ v)) = return $ ELitInt t (-1*v)
simplifyExpr (Not t b) | isSimpleBoolExpr b = return $ boolExpr t $ not $ fromBoolExpr b
simplifyExpr (EAdd t (EString _ s1) Plus{} (EString _ s2)) = return $ EString t (s1 ++ s2)
simplifyExpr (EAdd t (ELitInt _ v1) opr (ELitInt _ v2)) = return $ ELitInt t $ op opr v1 v2
simplifyExpr e@(EMul t ELitInt{} Div{} (ELitInt _ v)) | v == 0 = return e -- jednak nic nie robimy :) mThrowError "Cannot divide by zero"
simplifyExpr e@(EMul t ELitInt{} Mod{} (ELitInt _ v)) | v == 0 = return e -- mThrowError "Cannot mod by zero"
simplifyExpr (EMul t (ELitInt _ v1) opr (ELitInt _ v2)) = return $ ELitInt t $ op opr v1 v2
simplifyExpr (ERel t (ELitInt _ v1) opr (ELitInt _ v2)) = return $ boolExpr t $ op opr v1 v2
simplifyExpr (ERel t (EString _ s1) EQU{} (EString _ s2)) = return $ boolExpr t $ s1 == s2
simplifyExpr (ERel t (EString _ s1) NE{} (EString _ s2)) = return $ boolExpr t $ s1 /= s2

simplifyExpr (ERel t b1 EQU{} b2) | isSimpleBoolExpr b1 && isSimpleBoolExpr b2 =
  let (v1,v2) = (fromBoolExpr b1, fromBoolExpr b2) in return $ boolExpr t $ v1 == v2

simplifyExpr (ERel t b1 NE{} b2) | isSimpleBoolExpr b1 && isSimpleBoolExpr b2 =
  let (v1,v2) = (fromBoolExpr b1, fromBoolExpr b2) in return $ boolExpr t $ v1 /= v2

simplifyExpr (EAnd _ f@ELitFalse{} _) = return f
simplifyExpr (EAnd _ ELitTrue{} v) = return v
simplifyExpr (EOr _ t@ELitTrue{} _) = return t
simplifyExpr (EOr _ ELitFalse{} v) = return v
simplifyExpr (EAnd _ v ELitTrue{}) = return v
simplifyExpr (EOr _ v ELitFalse{}) = return v

simplifyExpr t = return $ t

