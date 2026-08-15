-- This implementation is adapted from
-- https://mathisbd.github.io/blog/esubstitutions.html
-- NOTE: Claude Fable 5 assisted with this implementation

{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Rebound.Env.ShiftSkewed where

import Data.Nat
import Data.Fin

import Rebound.Lib
import GHC.Generics hiding (S)
import Control.DeepSeq (NFData (..))

------------------------------------------------------------------------------
-- Substitution class declarations
------------------------------------------------------------------------------
-- | Well-scoped types that can be the range of
-- an environment. This should generally be the @Var@
-- constructor from the syntax.
class (Subst v v) => SubstVar (v :: Nat -> Type) where
  var :: Fin n -> v n


-- | Apply the environment throughout a term of
-- type `c n`, replacing variables with values
-- of type `v m`
class (SubstVar v) => Subst v c where
  applyE :: Env v n m -> c n -> c m
  default applyE :: (Generic1 c, GSubst v (Rep1 c), SubstVar v) => Env v m n -> c m -> c n
  applyE = gapplyE
  {-# INLINE applyE #-}
  isVar :: c n -> Maybe (v :~: c, Fin n)
  isVar _ = Nothing
  {-# INLINE isVar #-}

-- | Generic programming variant of 'applyE'.
gapplyE :: forall c v m n. (Generic1 c, GSubst v (Rep1 c), Subst v c) => Env v m n -> c m -> c n
gapplyE r e | Just (Refl, x) <- isVar @v @c e = applyEnv r x
gapplyE r e = applyOpt (\s x -> to1 $ gsubst s (from1 x)) r e
{-# INLINEABLE gapplyE #-}

-- | Generic programming support for 'Subst'.
class GSubst v (e :: Nat -> Type) where
  gsubst :: Env v m n -> e m -> e n

------------------------------------------------------------------------------
-- Environment representation
------------------------------------------------------------------------------

-- | A complete binary tree storing @S w@ terms.
--
-- A tree is a /sequence/ of entries: the root's term comes first, then the
-- entries of the left subtree, then those of the right subtree. Each node
-- records a shift @k@ that applies to everything underneath it, and caches the
-- total shift of the whole tree (@k + k1 + k2@). Because the entries are
-- sequenced, the base scope of the left subtree is the /range/ of the right
-- subtree, exactly as in the cons-list version.
data Tree :: (Nat -> Type)
          -> Nat -- ^ one less than the number of terms stored in the tree
          -> Nat -- ^ total shift amount == k + total left + total right
          -> Nat -- ^ base scope of the range (the range itself is @k_tot + m@)
          -> Type where
  Leaf :: SNat k -> a m -> Tree a Z k m
  Node :: SNat k              -- ^ local shift amount for this node
       -> SNat (k + (k1 + k2)) -- ^ total shift amount (cached)
       -> SNat w              -- ^ size index of each subtree
       -> a (k1 + (k2 + m))
       -> Tree a w k1 (k2 + m)
       -> Tree a w k2 m
       -> Tree a (S (w + S w)) (k + (k1 + k2)) m

-- | The total shift stored in a tree. This is cached at each node, so it is
-- constant time.
totalOffset :: Tree a w k m -> SNat k
totalOffset (Leaf k _) = k
totalOffset (Node _ kt _ _ _ _) = kt

-- The 'SNat k' in this representation is an embedded shift
-- that means that 'Inc k' is the same as 'Inc k'
data Env a m n where
    Zero :: Env a Z n
    Inc  :: !(SNat k) -> Env a n (k + n)
    Cons :: !(SNat w) -- ^ size index of the tree (it stores @S w@ terms)
         -> Tree a w k m -> Env a n m -> Env a (S (w + n)) (k + m)

instance (forall n. NFData (a n)) => NFData (Env a n m) where
  rnf :: (forall (n1 :: Nat). NFData (a n1)) => Env a n m -> ()
  rnf Zero = ()
  rnf (Inc x) = rnf x
  rnf (Cons k x xs) = rnf k `seq` rnf x `seq` rnf xs

instance (forall n. NFData (a n)) => NFData (Tree a n k m) where
  rnf :: (forall (n1 :: Nat). NFData (a n1)) => Tree a n k m -> ()
  rnf (Leaf k a) = rnf k `seq` rnf a
  rnf (Node k kt n a l r) = rnf k `seq` rnf a `seq` rnf l `seq` rnf r

------------------------------------------------------------------------------
-- Application
------------------------------------------------------------------------------

weaken :: forall a k n. Subst a a => SNat k -> a n -> a (k + n)
weaken k t = applyE @a (shiftNE k) t

applyEnv ::  SubstVar a => Env a n m -> Fin n -> a m
applyEnv s i = applyRec @N0 snat s i
{-# INLINEABLE applyEnv #-}

-- | Build an optimized version of applyE.
-- Checks to see if we are applying the identity substitution first.
applyOpt :: (Env v n m -> c n -> c m) -> (Env v n m -> c n -> c m)
applyOpt f (Inc SZ) x = x
applyOpt f r x = f r x
{-# INLINEABLE applyOpt #-}


-- | Look up the @i@th entry of a tree, under an accumulated shift of @acc@.
applyTree :: forall acc a w k m . SubstVar a =>
    SNat acc -> Tree a w k m -> Fin (S w) -> a (acc + (k + m))
applyTree acc s i =
  case s of
    Leaf (k :: SNat k0) (t :: a m0)
      | Refl <- axiomAssoc @acc @k0 @m0 ->
        case i of
          FZ   -> weaken (sPlus acc k) t  -- substitution
          FS j -> case j of {}
    Node (k :: SNat k0) _ (w :: SNat w0) (t :: a (k1 + (k2 + m0)))
         (l :: Tree a w0 k1 (k2 + m0)) (r :: Tree a w0 k2 m0)
      | Refl <- axiomAssoc @k1 @k2 @m0
      , Refl <- axiomAssoc @k0 @(k1 + k2) @m0
      , Refl <- axiomAssoc @acc @k0 @(k1 + (k2 + m0))
      , Refl <- axiomAssoc @(acc + k0) @k1 @(k2 + m0) ->
        case i of
          FZ -> weaken (sPlus acc k) t
          FS j -> withSNat (next w) $ case split @(S w0) @(S w0) j of
               Left j0  -> applyTree (sPlus acc k) l j0
               Right j0 -> applyTree (sPlus (sPlus acc k) (totalOffset l)) r j0


-- | As we traverse the list, accumulate the shifting amount and
-- apply it all at once.
applyRec :: forall acc a n m . SubstVar a =>
    SNat acc -> Env a n m -> Fin n -> a (acc + m)
applyRec acc s i =
    case s of
        Zero -> case i of {}
        Inc (k :: SNat k) -- renaming
              | Refl <- axiomAssoc @acc @k @n
              -> var (shiftN (sPlus acc k) i)
        Cons (w :: SNat w) (t :: Tree a w k m1) (s' :: Env a n2 m1)
              | Refl <- axiomAssoc @acc @k @m1
              -> withSNat (next w) $ case split @(S w) @n2 i of
                   Left j0  -> applyTree acc t j0
                   Right j0 -> applyRec (sPlus acc (totalOffset t)) s' j0


zeroE :: Env a Z n
zeroE = Zero
{-# INLINEABLE zeroE #-}


shiftNE :: SNat k -> Env a n (k + n)
shiftNE k = Inc k
{-# INLINEABLE shiftNE #-}


-- | @cons@ -- extend an environment with a new mapping for index '0'.
-- When the two leading trees have the same size they are merged into a single
-- tree, which keeps the list skew-binary (and lookup logarithmic).
(.:) :: forall a n m. a m -> Env a n m -> Env a (S n) m
x .: (Cons (w1 :: SNat w1) (l :: Tree a w1 k1 m1)
           (Cons (w2 :: SNat w2) (r :: Tree a w2 k2 m2) (rest :: Env a n3 m2)))
  | Just Refl <- testEquality w1 w2
  , Refl <- axiomAssoc @k1 @k2 @m2
  , Refl <- axiomAssoc @w1 @(S w1) @n3
  = Cons (next (sPlus w1 (next w1)))
         (Node SZ (sPlus (totalOffset l) (totalOffset r)) w1 x l r)
         rest
x .: s = Cons SZ (Leaf SZ x) s
{-# INLINEABLE (.:) #-}

-- | Add @k0@ to the shift stored at the root of a tree. Constant time.
bumpTree :: forall k0 a w k m. SNat k0 -> Tree a w k m -> Tree a w (k0 + k) m
bumpTree k0 (Leaf k t) = Leaf (sPlus k0 k) t
bumpTree k0 (Node (k :: SNat k') kt (w :: SNat w') t
                  (l :: Tree a w' k1 (k2 + m)) (r :: Tree a w' k2 m))
  | Refl <- axiomAssoc @k0 @k' @(k1 + k2)
  = Node (sPlus k0 k) (sPlus k0 kt) w t l r

-- | inverse of @cons@ -- remove the first mapping.
-- Splitting the leading tree into its two subtrees restores the skew-binary
-- shape, so this is constant time.
tailEnv :: forall a n m. Env a (S n) m -> Env a n m
tailEnv (Inc (k :: SNat k))
  -- the range is @k + S n@, i.e. @k + (N1 + n)@, which associates to @(k + N1) + n@
  | Refl <- axiomAssoc @k @N1 @n
  = Inc (sPlus k s1)
tailEnv (Cons (w :: SNat w) t (s :: Env a n2 m1)) =
  case t of
    Leaf (k :: SNat k) _ -> withSNat k $ skip0 @k s
    Node (k0 :: SNat k0) _ (w' :: SNat w') _
         (l :: Tree a w' k1 (k2 + m1)) (r :: Tree a w' k2 m1)
      | Refl <- axiomAssoc @w' @(S w') @n2
      , Refl <- axiomAssoc @k1 @k2 @m1
      , Refl <- axiomAssoc @k0 @(k1 + k2) @m1
      , Refl <- axiomAssoc @k0 @k1 @(k2 + m1)
      -> Cons w' (bumpTree k0 l) (Cons w' r s)

-- | inverse of @cons@ -- remove the first mapping
tail :: (SubstVar v) => Env v (S n) m -> Env v n m
tail = tailEnv
{-# INLINEABLE tail #-}

-- | Remove the first @k@ mappings.
dropEnv :: forall k a n m. SNat k -> Env a (k + n) m -> Env a n m
dropEnv k s = case snat_ k of
    SZ_    -> s
    SS_ k' -> dropEnv k' (tailEnv s)

-- Compose a substitution with shifting, just add the shifting amount
-- to the head of the substitution
-- skip k s == s .>> Inc k
skip0 :: forall k0 a n m. SNatI k0 => Env a n m -> Env a n (k0 + m)
skip0 s = case s of
              Zero -> Zero
              (Inc (k :: SNat k))
                | Refl <- axiomAssoc @k0 @k @n
                    -> Inc (sPlus (snat @k0) k)
              (Cons (w :: SNat w) (t :: Tree a w k m1) s')
                | Refl <- axiomAssoc @k0 @k @m1
                    -> Cons w (bumpTree (snat @k0) t) s'
{-# INLINEABLE skip0 #-}

-- | Adapt an environment to go under a binder.
-- Going under a binder with the identity leaves it unchanged, so descending
-- through many binders does not grow the environment.
up :: forall a n m. SubstVar a => Env a n m -> Env a (S n) (S m)
up (Inc SZ) = Inc SZ
up s = var f0 .: (skip0 @N1 s)

-- NB: there is a generic definition of upN in Env.hs, but I don't know
-- how efficient it is.

-- | Compose two environments, applying them in sequence (left then right).
(.>>) :: (SubstVar v) => Env v p n -> Env v n m -> Env v p m
(.>>) = comp
{-# INLINEABLE (.>>) #-}

-- | Apply an environment to every entry of a tree, preserving the shape of the
-- tree. The result stores no shifts at all, as they have all been applied.
substTree :: forall acc a w k m p. SubstVar a =>
    SNat acc -> Tree a w k m -> Env a (acc + (k + m)) p -> Tree a w Z p
substTree acc t s =
  case t of
    Leaf (k :: SNat k0) (x :: a m0)
      | Refl <- axiomAssoc @acc @k0 @m0
      -> Leaf SZ (applyE s (weaken (sPlus acc k) x))
    Node (k :: SNat k0) _ (w :: SNat w0) (x :: a (k1 + (k2 + m0)))
         (l :: Tree a w0 k1 (k2 + m0)) (r :: Tree a w0 k2 m0)
      | Refl <- axiomAssoc @k1 @k2 @m0
      , Refl <- axiomAssoc @k0 @(k1 + k2) @m0
      , Refl <- axiomAssoc @acc @k0 @(k1 + (k2 + m0))
      , Refl <- axiomAssoc @(acc + k0) @k1 @(k2 + m0)
      -> Node SZ SZ w (applyE s (weaken (sPlus acc k) x))
              (substTree (sPlus acc k) l s)
              (substTree (sPlus (sPlus acc k) (totalOffset l)) r s)

-- | look at the two arguments and compose them together smartly
comp :: forall a m n p. (SubstVar a) =>
         Env a m n -> Env a n p -> Env a m p
comp Zero s = Zero
-- if the second argument is a shift, we can use skip
comp s (Inc (k :: SNat k)) = withSNat k $ skip0 @k s
-- if the first argument is a shift, we can drop entries from the second
-- argument
comp (Inc k) s = dropEnv k s
-- otherwise, apply the second substitution to every entry of the first
comp (Cons (w :: SNat w) (t :: Tree a w k m1) (xs :: Env a n2 m1)) s =
    withSNat (totalOffset t) $
      Cons w (substTree SZ t s) (comp (skip0 @k xs) s)

-- | Map the range of an environment. Has to preserve the scope of the range.
transform :: (SubstVar b) =>
   (forall m. a m -> b m) -> Env a n m -> Env b n m
transform f Zero = Zero
transform f (Inc k) = Inc k
transform f (Cons k xs s) = Cons k (transformTree f xs) (transform f s)

transformTree :: (SubstVar b) =>
   (forall m. a m -> b m) -> Tree a n k m -> Tree b n k m
transformTree f (Leaf k x) = Leaf k (f x)
transformTree f (Node k kt n x l r) = Node k kt n (f x) (transformTree f l) (transformTree f r)
