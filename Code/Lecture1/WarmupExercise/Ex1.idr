import Decidable.Equality
import Syntax.PreorderReasoning

-- This is the (simplified) definition of names in Core.TT
data Name : Type where
     UN : String -> Name -- user written name
     MN : String -> Int -> Name -- machine generated name

-- 1. Write an Eq instance for Name
-- (sorry, it's not derivable yet!)
Eq Name where
  (UN n) == (UN n') = n == n'
  (MN m i) == (MN m' i') = m == m' && i == i'
  _ == _ = False

-- 2. Sometimes, we need to compare names for equality and use a proof that
-- they're equal. So, implement the following
nameEq : (x : Name) -> (y : Name) -> Maybe (x = y)

-- 3. (Optional, since we don't need this in Idris 2, but it's a good
-- exercise to see if you can do it!) Implement decidable equality, so you
-- also have a proof if names are *not* equal.
DecEq Name where
  decEq (UN n)   (UN n') with (decEq n n')
    decEq (UN n)   (UN n') | (Yes prf) = Yes (cong UN prf)
    decEq (UN n)   (UN n') | (No contra) = No (\case Refl => contra Refl)
  decEq (MN m i) (MN m' i') with (decEq m m')
    decEq (MN m i) (MN m' i') | (No contra) = No (\case Refl => contra Refl)
    decEq (MN m i) (MN m' i') | (Yes prf) with (decEq i i')
      decEq (MN m i) (MN m' i') | (Yes prf1) | (Yes prf2) = Yes (cong2 MN prf1 prf2)
      decEq (MN m i) (MN m' i') | (Yes prf1) | (No contra) = No (\case Refl => contra Refl)
  decEq (UN n)   (MN m' i') = No (\case Refl impossible)
  decEq (MN m i) (UN n') = No (\case Refl impossible)

nameEq x y with (decEq x y)
  nameEq x y | (Yes prf) = Just prf
  nameEq x y | (No contra) = Nothing
