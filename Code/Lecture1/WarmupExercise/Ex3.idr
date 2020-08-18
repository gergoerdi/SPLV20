
-- 1. Prove that appending Nil is the identity
-- (Note: this is defined in Data.List, but have a go yourself!)
appendNilNeutral : (xs : List a) -> xs ++ [] = xs
appendNilNeutral [] = Refl
appendNilNeutral (x :: xs) = cong (x ::) (appendNilNeutral xs)

-- 2. Prove that appending lists is associative.
-- (Note: also defined in Data.List)
appendAssoc : (xs : List a) -> (ys : List a) -> (zs : List a) ->
              xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
appendAssoc [] ys zs = Refl
appendAssoc (x :: xs) ys zs = cong (x ::) (appendAssoc xs ys zs)

-- A tree indexed by the (inorder) flattening of its contents
data Tree : List a -> Type where
     Leaf : Tree []
     Node : Tree xs -> (x : a) -> Tree ys -> Tree (xs ++ x :: ys)

-- 3. Fill in rotateLemma. You'll need appendAssoc.
rotateL : Tree xs -> Tree xs
rotateL Leaf = Leaf
rotateL (Node left n Leaf) = Node left n Leaf
rotateL (Node {xs = xs} {ys = ys ++ n' :: zs} left n (Node {xs = ys} {ys = zs} rightl n' rightr))
    = replace {p = Tree} prf $ Node (Node left n rightl) n' rightr
  where
    0 prf : (xs ++ (n :: ys)) ++ (n' :: zs) = xs ++ ((n :: ys) ++ (n' :: zs))
    prf = sym $ appendAssoc _ _ _

-- 4. Complete the definition of rotateR
rotateR : Tree xs -> Tree xs
rotateR Leaf = Leaf
rotateR (Node Leaf n right) = Node Leaf n right
rotateR (Node {xs = xs ++ n' :: ys} {ys = zs} (Node leftl n' leftr) n right) = replace {p = Tree} prf $ Node leftl n' (Node leftr n right)
  where
    0 prf : xs ++ ((n' :: ys) ++ (n :: zs)) = (xs ++ (n' :: ys)) ++ (n :: zs)
    prf = appendAssoc _ _ _
