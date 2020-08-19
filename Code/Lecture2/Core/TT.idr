module Core.TT

import Data.List
import Decidable.Equality

-- In Idris2, this is defined in Core.Name
public export
data Name : Type where
     UN : String -> Name -- user written name
     MN : String -> Int -> Name -- machine generated name

export
nameEq : (x : Name) -> (y : Name) -> Maybe (x = y)
nameEq (UN x) (UN y) with (decEq x y)
  nameEq (UN y) (UN y) | (Yes Refl) = Just Refl
  nameEq (UN x) (UN y) | (No contra) = Nothing
nameEq (MN x t) (MN x' t') with (decEq x x')
  nameEq (MN x t) (MN x t') | (Yes Refl) with (decEq t t')
    nameEq (MN x t) (MN x t) | (Yes Refl) | (Yes Refl) = Just Refl
    nameEq (MN x t) (MN x t') | (Yes Refl) | (No contra) = Nothing
  nameEq (MN x t) (MN x' t') | (No contra) = Nothing
nameEq _ _ = Nothing

export
Eq Name where
  (==) (UN x) (UN y) = x == y
  (==) (MN x i) (MN y j) = i == j && x == y
  (==) _ _ = False

nameTag : Name -> Int
nameTag (UN _) = 0
nameTag (MN _ _) = 1

export
Ord Name where
  compare (UN x) (UN y) = compare x y
  compare (MN x i) (MN y j)
      = case compare x y of
             EQ => compare i j
             t => t
  compare x y = compare (nameTag x) (nameTag y)

public export
data NameType : Type where
     Func : NameType
     Bound : NameType
     DataCon : (tag : Int) -> (arity : Nat) -> NameType
     TyCon : (tag : Int) -> (arity : Nat) -> NameType

export
Show NameType where
  show Func = "Func"
  show (DataCon t a) = "DataCon " ++ show (t, a)
  show (TyCon t a) = "TyCon " ++ show (t, a)
  show Bound = "Bound"

public export
data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)

public export
dropVar : (ns : List Name) -> {idx : Nat} ->
          (0 p : IsVar name idx ns) -> List Name
dropVar [] p = []
dropVar (n :: ns) First = ns
dropVar (n :: ns) (Later p) = dropVar ns p

public export
data Var : List Name -> Type where
     MkVar : {i : Nat} -> (0 p : IsVar n i vars) -> Var vars

public export
data PiInfo : Type where
     Implicit : PiInfo
     Explicit : PiInfo

public export
data Binder : Type -> Type where
     Lam : PiInfo -> ty -> Binder ty
     Pi : PiInfo -> ty -> Binder ty

     PVar : ty -> Binder ty -- pattern bound variables ...
     PVTy : ty -> Binder ty -- ... and their type

export
Functor Binder where
  map func (Lam pi ty) = Lam pi (func ty)
  map func (Pi pi ty) = Pi pi (func ty)
  map func (PVar ty) = PVar (func ty)
  map func (PVTy ty) = PVTy (func ty)

export
Foldable Binder where
  foldr f s (Lam pi ty) = f ty s
  foldr f s (Pi pi ty) = f ty s
  foldr f s (PVar ty) = f ty s
  foldr f s (PVTy ty) = f ty s

export
Traversable Binder where
  traverse f (Lam pi ty) = Lam pi <$> f ty
  traverse f (Pi pi ty) = Pi pi <$> f ty
  traverse f (PVar ty) = PVar <$> f ty
  traverse f (PVTy ty) = PVTy <$> f ty

public export
data Term : List Name -> Type where
     Local : (idx : Nat) -> -- de Bruijn index
             (0 p : IsVar name idx vars) -> -- proof that index is valid
             Term vars
     Ref : (nt : NameType) -> (x : Name) -> Term vars -- a reference to a global name
     Meta : (x : Name) -> (ts : List (Term vars)) -> Term vars
     Bind : (x : Name) -> -- any binder, e.g. lambda or pi
            (b : Binder (Term vars)) ->
            (scope : Term (x :: vars)) -> -- one more name in scope
            Term vars
     App : (f : Term vars) -> (e : Term vars) -> Term vars -- function application
     TType : Term vars
     Erased : Term vars

-- Term manipulation

weakenVar : {inner : List Name} -> Var (inner ++ outer) -> Var (inner ++ [x] ++ outer)
weakenVar {inner = []} (MkVar p) = MkVar (Later p)
weakenVar {inner = (_::xs)} (MkVar First) = MkVar First
weakenVar {inner = (_::xs)} {x = x} (MkVar (Later p)) with (weakenVar {x = x} (MkVar p))
  weakenVar {inner = (_::xs)} {  x = x} (MkVar (Later p)) | (MkVar p') = MkVar (Later p')

weaken' : {inner : List Name} -> Term (inner ++ outer) -> Term (inner ++ [x] ++ outer)
weaken' (Local idx p) with (weakenVar {inner = inner} {x = x} (MkVar p))
  weaken' (Local idx p) | (MkVar p') = Local _ p'
weaken' (Ref nt n) = Ref nt n
weaken' (Meta n ts) = Meta n $ map weaken' ts
weaken' (Bind n b scope) = Bind n (map weaken' b) (weaken' {inner = _ :: _} scope)
weaken' (App f e) = App (weaken' f) (weaken' e)
weaken' TType = TType
weaken' Erased = Erased

export
weaken : Term vars -> Term (x :: vars)
weaken = weaken' {inner = []}

embedIsVar : IsVar name idx vars -> IsVar name idx (vars ++ more)
embedIsVar First = First
embedIsVar (Later p) = Later $ embedIsVar p

export
embed : Term vars -> Term (vars ++ more)
embed (Local idx p) = Local idx $ embedIsVar p
embed (Ref nt x) = Ref nt x
embed (Meta x ts) = Meta x $ map embed ts
embed (Bind x b scope) = Bind x (map embed b) (embed scope)
embed (App f e) = App (embed f) (embed e)
embed TType = TType
embed Erased = Erased

contractVar : {inner : List Name} -> Var (inner ++ [x] ++ outer) -> Maybe (Var (inner ++ outer))
contractVar {inner = []} (MkVar First) = Nothing
contractVar {inner = []} (MkVar (Later p)) = pure $ MkVar p
contractVar {inner = (x::xs)} (MkVar First) = pure $ MkVar First
contractVar {inner = (x::xs)} (MkVar (Later p)) = do
    MkVar p' <- contractVar {inner = xs} (MkVar p)
    pure $ MkVar (Later p')

contract' : {inner : List Name} -> Term (inner ++ [x] ++ outer) -> Maybe (Term (inner ++ outer))
contract' (Local idx p) = do
    MkVar p' <- contractVar (MkVar p)
    pure $ Local _ p'
contract' (Ref nt x) = pure $ Ref nt x
contract' (Meta x ts) = Meta x <$> traverse contract' ts
contract' (Bind x b scope) = Bind x <$> traverse contract' b <*> contract' {inner = _ :: _} scope
contract' (App f e) = App <$> contract' f <*> contract' e
contract' TType = pure TType
contract' Erased = pure Erased

export
contract : Term (x :: vars) -> Maybe (Term vars)
contract = contract' {inner = []}

subst' : {inner : List Name} -> Term (inner ++ outer) -> Term (inner ++ [x] ++ outer) -> Term (inner ++ outer)
subst' e0 (Local idx p) = case contractVar (MkVar p) of
    Nothing => e0
    Just (MkVar p') => Local _ p'
subst' e0 (Ref nt x) = Ref nt x
subst' e0 (Meta x ts) = Meta x $ map (subst' e0) ts
subst' {inner} e0 (Bind x b scope) = Bind x (map (subst' e0) b) (subst' {inner = _ :: _} (weaken e0) scope)
subst' e0 (App f e) = App (subst' e0 f) (subst' e0 e)
subst' e0 TType = TType
subst' e0 Erased = Erased

export
subst : Term vars -> Term (x :: vars) -> Term vars
subst = subst' {inner = []}

public export
data CompatibleVars : List Name -> List Name -> Type where
     CompatPre : CompatibleVars xs xs
     CompatExt : CompatibleVars xs ys -> CompatibleVars (n :: xs) (m :: ys)

renameVar : CompatibleVars xs ys -> Var xs -> Var ys
renameVar CompatPre v = v
renameVar (CompatExt c) (MkVar First) = MkVar First
renameVar (CompatExt c) (MkVar (Later p)) with (renameVar c (MkVar p))
  renameVar (CompatExt c) (MkVar (Later p)) | (MkVar p') = MkVar (Later p')

export
renameVars : CompatibleVars xs ys -> Term xs -> Term ys
renameVars c (Local idx p) with (renameVar c (MkVar p))
  renameVars c (Local idx p) | (MkVar p') = Local _ p'
renameVars c (Ref nt x) = Ref nt x
renameVars c (Meta x ts) = Meta x $ map (renameVars c) ts
renameVars c (Bind x b scope) = Bind x (map (renameVars c) b) (renameVars (CompatExt c) scope)
renameVars c (App f e) = App (renameVars c f) (renameVars c e)
renameVars c TType = TType
renameVars c Erased = Erased

--- Show instances

export
getFnArgs : Term vars -> (Term vars, List (Term vars))
getFnArgs tm = getFA [] tm
  where
    getFA : List (Term vars) -> Term vars ->
            (Term vars, List (Term vars))
    getFA args (App f a) = getFA (a :: args) f
    getFA args tm = (tm, args)

export
showSep : String -> List String -> String
showSep sep [] = ""
showSep sep [x] = x
showSep sep (x :: xs) = x ++ sep ++ showSep sep xs

export
Show Name where
  show (UN n) = n
  show (MN n i) = "{" ++ n ++ ":" ++ show i ++ "}"

export
nameAt : {vars : _} ->
         (idx : Nat) -> (0 p : IsVar n idx vars) -> Name
nameAt {vars = n :: ns} Z First = n
nameAt {vars = n :: ns} (S k) (Later p) = nameAt k p

export
{vars : _} -> Show (Term vars) where
  show tm = let (fn, args) = getFnArgs tm in showApp fn args
    where
      showApp : {vars : _} -> Term vars -> List (Term vars) -> String
      showApp (Local {name} idx p) []
         = show (nameAt idx p) ++ "[" ++ show idx ++ "]"
      showApp (Ref _ n) [] = show n
      showApp (Meta n args) []
          = "?" ++ show n ++ "_" ++ show args
      showApp (Bind x (Lam p ty) sc) []
          = "\\" ++ show x ++ " : " ++ show ty ++
            " => " ++ show sc
      showApp (Bind x (Pi Explicit ty) sc) []
          = "((" ++ show x ++ " : " ++ show ty ++
            ") -> " ++ show sc ++ ")"
      showApp (Bind x (Pi Implicit ty) sc) []
          = "{" ++ show x ++ " : " ++ show ty ++
            "} -> " ++ show sc
      showApp (Bind x (PVar ty) sc) []
          = "pat " ++ show x ++ " : " ++ show ty ++
            " => " ++ show sc
      showApp (Bind x (PVTy ty) sc) []
          = "pty " ++ show x ++ " : " ++ show ty ++
            " => " ++ show sc
      showApp (App _ _) [] = "[can't happen]"
      showApp TType [] = "Type"
      showApp Erased [] = "[_]"
      showApp _ [] = "???"
      showApp f args = "(" ++ assert_total (show f) ++ " " ++
                        assert_total (showSep " " (map show args))
                     ++ ")"
