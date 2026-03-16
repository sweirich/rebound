{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Rebound.Env.SkewedList where

import Data.Kind (Type)
import Data.Nat
import Data.Fin
import Data.SNat
import Data.Type.Equality
import Data.Foldable
import Prelude hiding (lookup)

-- A skewed list containing elements of type a, indexed by the number
-- of elements n.
-- In a skewed list Cons (n1, t1, Cons (n2, t2, Cons (n3, t3, ...)))
-- we maintain the invariant that the trees t1, t2, t3, … are
-- complete binary trees of increasing sizes, and at most the
-- first two trees can have the same size. Thanks to this invariant,
-- in a skewed list with n elements the number of Cons cells is
-- O(log n) and the depth of each tree is O(log n).

-- | A complete binary tree with exactly n elements.
-- Node carries the subtree size singleton, needed for routing during lookup.
data Tree :: Nat -> Type -> Type where
  Leaf :: a -> Tree N1 a
  Node :: SNat n -> a -> Tree n a -> Tree n a -> Tree (S (n + n)) a

deriving instance (Show a) => Show (Tree n a)
deriving instance (Functor (Tree n)) 
deriving instance (Foldable (Tree n))

-- | A skewed list with exactly n elements.
data SkewedList :: Nat -> Type -> Type where
  Nil  :: SkewedList Z a
  Cons :: SNat w -> Tree w a -> SkewedList m a -> SkewedList (w + m) a

deriving instance (Show a) => Show (SkewedList n a)
deriving instance (Functor (SkewedList n)) 
deriving instance (Foldable (SkewedList n))  

size :: SkewedList n a -> SNat n
size Nil = SZ
size (Cons sz _ sl) = sPlus sz (size sl)

-- | The empty skewed list.
nil :: SkewedList Z a
nil = Nil

-- | Add an element to the front of a skewed list.
-- When the first two trees have equal size w, they are merged into a
-- single tree of size S(w+w), using axiomAssoc to discharge
-- the proof obligation  w + (w + m) ~ (w + w) + m.
cons :: a -> SkewedList n a -> SkewedList (S n) a
cons x (Cons (w1 :: SNat w) t1 (Cons w2 t2 (rest :: SkewedList m a)))
  | Just Refl <- testEquality w1 w2
  = case axiomAssoc @w @w @m of
      Refl -> Cons (next (sPlus w1 w1)) (Node w1 x t1 t2) rest
cons x list = Cons s1 (Leaf x) list

-- | remove the first element of a non empty tree and return its tail
unCons :: SkewedList (S n) a -> (a, SkewedList n a)
unCons (Cons _ (Leaf x) sl) = (x, sl)
unCons (Cons _ (Node (w1 :: SNat w1) x l r) (sl :: SkewedList m a)) 
   | Refl <- axiomAssoc @w1 @w1 @m 
   = (x, (Cons w1 l (Cons w1 r sl)))

-- | Lookup the [i]-th element in a skewed list.
-- The Fin index statically guarantees the lookup is in bounds.
lookup :: Fin n -> SkewedList n a -> a
lookup i Nil = absurd i
lookup i (Cons (w :: SNat w) t (rest :: SkewedList m a)) =
  withSNat w $ case split @w i of
    Left  j -> lookupTree j t
    Right j -> lookup j rest

-- | Lookup the [i]-th element in a complete binary tree of size n.
lookupTree :: Fin n -> Tree n a -> a
lookupTree FZ     (Leaf x)                            = x
lookupTree (FS i) (Leaf _)                            = absurd i
lookupTree FZ     (Node _ x _ _)                      = x
lookupTree (FS i) (Node (sz :: SNat n) _ l r)         =
  withSNat sz $ case split i of   -- compare i < sz
    Left  j -> lookupTree j l
    Right j -> lookupTree j r


tree = cons "A" (cons "B" (cons "C" (cons "D" (cons "E" nil))))

-- >>> tree
-- Cons SS (Leaf "A") (Cons SS (Leaf "B") (Cons SS (Node SS "C" (Leaf "D") (Leaf "E")) Nil))

-- >>> toList tree
-- ["A","B","C","D","E"]

-- >>> length tree
-- 5

-- >>> toInt (size tree)
-- 5
