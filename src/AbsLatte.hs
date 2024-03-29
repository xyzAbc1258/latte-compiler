

module AbsLatte where

-- Haskell module generated by the BNF converter




newtype Ident = Ident String deriving (Eq, Ord, Show, Read)
data Program a = Program a [TopDef a]
  deriving (Eq, Ord, Show, Read)

instance Functor Program where
    fmap f x = case x of
        Program a topdefs -> Program (f a) (map (fmap f) topdefs)
data TopDef a
    = FnDef a (Type a) Ident [Arg a] (Block a)
    | ClDef a Ident (Ext a) [ClDecl a]
    | Struct a Ident [Type a]
    | VirtArray a Ident [FuncDec a]
  deriving (Eq, Ord, Show, Read)

instance Functor TopDef where
    fmap f x = case x of
        FnDef a type_ ident args block -> FnDef (f a) (fmap f type_) ident (map (fmap f) args) (fmap f block)
        ClDef a ident ext cldecls -> ClDef (f a) ident (fmap f ext) (map (fmap f) cldecls)
        Struct a ident types -> Struct (f a) ident (map (fmap f) types)
        VirtArray a ident funcdecs -> VirtArray (f a) ident (map (fmap f) funcdecs)
data Arg a = Arg a (Type a) Ident
  deriving (Eq, Ord, Show, Read)

instance Functor Arg where
    fmap f x = case x of
        Arg a type_ ident -> Arg (f a) (fmap f type_) ident
data ClDecl a
    = ClFld a (Type a) Ident
    | ClFunc a (Type a) Ident [Arg a] (Block a)
  deriving (Eq, Ord, Show, Read)

instance Functor ClDecl where
    fmap f x = case x of
        ClFld a type_ ident -> ClFld (f a) (fmap f type_) ident
        ClFunc a type_ ident args block -> ClFunc (f a) (fmap f type_) ident (map (fmap f) args) (fmap f block)
data Ext a = NoExt a | ClassExt a Ident
  deriving (Eq, Ord, Show, Read)

instance Functor Ext where
    fmap f x = case x of
        NoExt a -> NoExt (f a)
        ClassExt a ident -> ClassExt (f a) ident
data FuncDec a = FuncDecl a (Type a) Ident [Type a]
  deriving (Eq, Ord, Show, Read)

instance Functor FuncDec where
    fmap f x = case x of
        FuncDecl a type_ ident types -> FuncDecl (f a) (fmap f type_) ident (map (fmap f) types)
data Block a = Block a [Stmt a]
  deriving (Eq, Ord, Show, Read)

instance Functor Block where
    fmap f x = case x of
        Block a stmts -> Block (f a) (map (fmap f) stmts)
data Stmt a
    = Empty a
    | BStmt a (Block a)
    | NamedBStmt a Ident (Block a)
    | Decl a (Type a) [Item a]
    | Ass a (Expr a) (Expr a)
    | Incr a (Expr a)
    | Decr a (Expr a)
    | Ret a (Expr a)
    | VRet a
    | Cond a (Expr a) (Stmt a)
    | CondElse a (Expr a) (Stmt a) (Stmt a)
    | While a (Expr a) (Stmt a)
    | For a (Type a) Ident (Expr a) (Stmt a)
    | SExp a (Expr a)
    | CondJump a (Expr a) Ident Ident
    | Jump a Ident
  deriving (Eq, Ord, Show, Read)

instance Functor Stmt where
    fmap f x = case x of
        Empty a -> Empty (f a)
        BStmt a block -> BStmt (f a) (fmap f block)
        NamedBStmt a ident block -> NamedBStmt (f a) ident (fmap f block)
        Decl a type_ items -> Decl (f a) (fmap f type_) (map (fmap f) items)
        Ass a expr1 expr2 -> Ass (f a) (fmap f expr1) (fmap f expr2)
        Incr a expr -> Incr (f a) (fmap f expr)
        Decr a expr -> Decr (f a) (fmap f expr)
        Ret a expr -> Ret (f a) (fmap f expr)
        VRet a -> VRet (f a)
        Cond a expr stmt -> Cond (f a) (fmap f expr) (fmap f stmt)
        CondElse a expr stmt1 stmt2 -> CondElse (f a) (fmap f expr) (fmap f stmt1) (fmap f stmt2)
        While a expr stmt -> While (f a) (fmap f expr) (fmap f stmt)
        For a type_ ident expr stmt -> For (f a) (fmap f type_) ident (fmap f expr) (fmap f stmt)
        SExp a expr -> SExp (f a) (fmap f expr)
        CondJump a expr ident1 ident2 -> CondJump (f a) (fmap f expr) ident1 ident2
        Jump a ident -> Jump (f a) ident
data Item a = NoInit a Ident | Init a Ident (Expr a)
  deriving (Eq, Ord, Show, Read)

instance Functor Item where
    fmap f x = case x of
        NoInit a ident -> NoInit (f a) ident
        Init a ident expr -> Init (f a) ident (fmap f expr)
data Type a
    = Int a
    | Str a
    | Bool a
    | Void a
    | Class a Ident
    | Array a (Type a)
    | Fun a (Type a) [Type a]
    | Ptr a (Type a)
  deriving (Eq, Ord, Show, Read)

instance Functor Type where
    fmap f x = case x of
        Int a -> Int (f a)
        Str a -> Str (f a)
        Bool a -> Bool (f a)
        Void a -> Void (f a)
        Class a ident -> Class (f a) ident
        Array a type_ -> Array (f a) (fmap f type_)
        Fun a type_ types -> Fun (f a) (fmap f type_) (map (fmap f) types)
        Ptr a type_ -> Ptr (f a) (fmap f type_)
data BranchV a = BranchVar a (Expr a) Ident
  deriving (Eq, Ord, Show, Read)

instance Functor BranchV where
    fmap f x = case x of
        BranchVar a expr ident -> BranchVar (f a) (fmap f expr) ident
data Expr a
    = ESwitch a (Expr a) (Expr a) (Expr a)
    | EPhi a [BranchV a]
    | EVar a Ident
    | ELitInt a Integer
    | ELitTrue a
    | ELitFalse a
    | EFldAcc a (Expr a) Ident
    | EArrAcc a (Expr a) (Expr a)
    | EApp a (Expr a) [Expr a]
    | EString a String
    | ENull a (Type a)
    | ENewObj a (Type a)
    | ENewArr a (Type a) (Expr a)
    | Neg a (Expr a)
    | Not a (Expr a)
    | EMul a (Expr a) (MulOp a) (Expr a)
    | EAdd a (Expr a) (AddOp a) (Expr a)
    | ERel a (Expr a) (RelOp a) (Expr a)
    | EAnd a (Expr a) (Expr a)
    | EOr a (Expr a) (Expr a)
    | EVirtCall a (Expr a) Integer [Expr a]
    | EFldNoAcc a (Expr a) Integer
  deriving (Eq, Ord, Show, Read)

instance Functor Expr where
    fmap f x = case x of
        ESwitch a cond ift iff -> ESwitch (f a) (fmap f cond) (fmap f ift) (fmap f iff)
        EPhi a branchvs -> EPhi (f a) (map (fmap f) branchvs)
        EVar a ident -> EVar (f a) ident
        ELitInt a integer -> ELitInt (f a) integer
        ELitTrue a -> ELitTrue (f a)
        ELitFalse a -> ELitFalse (f a)
        EFldAcc a expr ident -> EFldAcc (f a) (fmap f expr) ident
        EArrAcc a expr1 expr2 -> EArrAcc (f a) (fmap f expr1) (fmap f expr2)
        EApp a expr exprs -> EApp (f a) (fmap f expr) (map (fmap f) exprs)
        EString a string -> EString (f a) string
        ENull a type_ -> ENull (f a) (fmap f type_)
        ENewObj a type_ -> ENewObj (f a) (fmap f type_)
        ENewArr a type_ expr -> ENewArr (f a) (fmap f type_) (fmap f expr)
        Neg a expr -> Neg (f a) (fmap f expr)
        Not a expr -> Not (f a) (fmap f expr)
        EMul a expr1 mulop expr2 -> EMul (f a) (fmap f expr1) (fmap f mulop) (fmap f expr2)
        EAdd a expr1 addop expr2 -> EAdd (f a) (fmap f expr1) (fmap f addop) (fmap f expr2)
        ERel a expr1 relop expr2 -> ERel (f a) (fmap f expr1) (fmap f relop) (fmap f expr2)
        EAnd a expr1 expr2 -> EAnd (f a) (fmap f expr1) (fmap f expr2)
        EOr a expr1 expr2 -> EOr (f a) (fmap f expr1) (fmap f expr2)
        EVirtCall a expr integer exprs -> EVirtCall (f a) (fmap f expr) integer (map (fmap f) exprs)
        EFldNoAcc a expr integer -> EFldNoAcc (f a) (fmap f expr) integer
data AddOp a = Plus a | Minus a
  deriving (Eq, Ord, Show, Read)

instance Functor AddOp where
    fmap f x = case x of
        Plus a -> Plus (f a)
        Minus a -> Minus (f a)
data MulOp a = Times a | Div a | Mod a
  deriving (Eq, Ord, Show, Read)

instance Functor MulOp where
    fmap f x = case x of
        Times a -> Times (f a)
        Div a -> Div (f a)
        Mod a -> Mod (f a)
data RelOp a = LTH a | LE a | GTH a | GE a | EQU a | NE a
  deriving (Eq, Ord, Show, Read)

instance Functor RelOp where
    fmap f x = case x of
        LTH a -> LTH (f a)
        LE a -> LE (f a)
        GTH a -> GTH (f a)
        GE a -> GE (f a)
        EQU a -> EQU (f a)
        NE a -> NE (f a)
