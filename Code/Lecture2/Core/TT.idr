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
     Later : (p : IsVar n i ns) -> IsVar n (S i) (m :: ns)

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

Ren : List Name -> List Name -> Type
Ren vars1 vars2 = Var vars1 -> Var vars2

weakenVar : {inner : List Name} -> Var (inner ++ outer) -> Var (inner ++ [x] ++ outer)
weakenVar {inner = []} (MkVar p) = MkVar (Later p)
weakenVar {inner = (_::xs)} (MkVar First) = MkVar First
weakenVar {inner = (_::xs)} {x = x} (MkVar (Later p)) = case weakenVar {x=x} (MkVar p) of
  MkVar p' => MkVar (Later p')

wkRen : Ren vars1 vars2 -> Ren (x::vars1) (x::vars2)
wkRen ren (MkVar First) = MkVar First
wkRen ren (MkVar (Later p)) = weakenVar {inner = []} $ ren (MkVar p)

rename : Ren vars1 vars2 -> Term vars1 -> Term vars2
rename ren (Local idx p) = case ren (MkVar p) of MkVar p' => Local _ p'
rename ren (Ref nt x) = Ref nt x
rename ren (Meta x ts) = Meta x $ map (rename ren) ts
rename ren (Bind x b scope) = Bind x (map (rename ren) b) (rename (wkRen ren) scope)
rename ren (App f e) = App (rename ren f) (rename ren e)
rename ren TType = TType
rename ren Erased = Erased

export
weaken : Term vars -> Term (x :: vars)
weaken = rename $ \(MkVar p) => MkVar (Later p)

Sub : List Name -> List Name -> Type
Sub vars1 vars2 = Var vars1 -> Term vars2

wkSub : Sub vars1 vars2 -> Sub (x::vars1) (x::vars2)
wkSub sub (MkVar First) = Local _ First
wkSub sub (MkVar (Later p)) = weaken (sub (MkVar p))

substAll : (Sub vars1 vars2) -> Term vars1 -> Term vars2
substAll sub (Local idx p) = sub (MkVar p)
substAll sub (Ref nt x) = Ref nt x
substAll sub (Meta x ts) = Meta x (map (substAll sub) ts)
substAll sub (Bind x b scope) = Bind x (map (substAll sub) b) (substAll (wkSub sub) scope)
substAll sub (App f e) = App (substAll sub f) (substAll sub e)
substAll sub TType = TType
substAll sub Erased = Erased

export
embed : Term vars -> Term (vars ++ more)
embed = substAll $ \v => case ren v of MkVar p => Local _ p
  where
    ren : {0 vars : List Name} -> Var vars -> Var (vars ++ more)
    ren (MkVar First) = MkVar First
    ren (MkVar (Later p)) with (ren (MkVar p))
      ren (MkVar (Later p)) | (MkVar p') = MkVar $ Later p'

traverseTerm : (Applicative f) => (Var vars1 -> f (Term vars2)) -> (Term vars1 -> f (Term vars2))
traverseTerm go (Local idx p) = go (MkVar p)
traverseTerm go (Ref nt x) = pure $ Ref nt x
traverseTerm go (Meta x ts) = Meta x <$> traverse (traverseTerm go) ts
traverseTerm go (Bind x b scope) = Bind x <$> traverse (traverseTerm go) b <*> traverseTerm go' scope
  where
    go' : Var (x :: vars1) -> f (Term (x :: vars2))
    go' (MkVar First) = pure $ Local _ First
    go' (MkVar (Later p)) = weaken <$> go (MkVar p)
traverseTerm go (App f e) = App <$> traverseTerm go f <*> traverseTerm go e
traverseTerm go TType = pure TType
traverseTerm go Erased = pure Erased

public export
interface RFunctor (v : k -> Type) (t : k -> Type) where
  rmap : (v a -> v b) -> t a -> t b

public export
interface (RFunctor v t) => RMonad (v : k -> Type) (t : k -> Type) where
  rpure : v a -> t a
  rbind : (v a -> t b) -> t a -> t b

interface RTraversable (v : k -> Type) (t : k -> Type) where
  rtraverse : (Applicative f) => (v a -> f (t b)) -> (t a -> f (t b))

export
RFunctor Var Term where
  rmap = rename

export
RMonad Var Term where
  rpure (MkVar p) = Local _ p
  rbind = substAll

export
RTraversable Var Term where
  rtraverse = traverseTerm

contractVar : {inner : List Name} -> Var (inner ++ [x] ++ outer) -> Maybe (Var (inner ++ outer))
contractVar {inner = []} (MkVar First) = Nothing
contractVar {inner = []} (MkVar (Later p)) = pure $ MkVar p
contractVar {inner = (x::xs)} (MkVar First) = pure $ MkVar First
contractVar {inner = (x::xs)} (MkVar (Later p)) = do
    MkVar p' <- contractVar {inner = xs} (MkVar p)
    pure $ MkVar (Later p')

export
contract : Term (x :: vars) -> Maybe (Term vars)
contract = traverseTerm $ \v => do
  MkVar p <- contractVar {inner = []} v
  pure $ Local _ p

export
subst : Term vars -> Term (x :: vars) -> Term vars
subst t0 = substAll $ \v => case v of
 MkVar First => t0
 MkVar (Later p) => Local _ p

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
renameVars c = substAll sub
  where
    sub : Sub xs ys
    sub v = case renameVar c v of MkVar p => Local _ p

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
