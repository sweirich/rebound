-- |
-- Module      : Rebound.Env.Rocq
-- Description : Explicit substitutions, ported from the Rocq kernel
--
-- A Haskell translation of the explicit-substitution machinery from the Rocq
-- (formerly Coq) kernel (originally written by Bruno Barras, Mar 2001),
-- adapted to use well-scoped types.
--
-- __Well-scoping__:
--
--  * @'Lift' src tgt@ maps every @'Fin' src@ index to a @'Fin' tgt@ index, and
--    'relocRel' enforces this.
--  * @'Subs' a n m@ maps every @'Fin' n@ index to a value in scope @m@. As in
--    "Rebound.Env.ShiftSkewed", the shifts embedded in the skewed tree are
--    tracked at the type level: @'Tree' a w k m@ stores @S w@ entries whose
--    base scope is @m@ and whose total shift is @k@, so the tree covers scope
--    @k + m@.
--
-- Because the shifts are tracked, no coercions are needed: the arithmetic is
-- discharged with 'axiomAssoc' from "Data.SNat".
{-# OPTIONS_HADDOCK hide #-}
module Rebound.Env.Rocq where

import Data.Fin (Fin (..))
import Data.Fin qualified as Fin
import Data.Proxy (Proxy (..))
import Data.SNat
import Data.Type.Equality

------------------------------------------------------------------------
-- * Lifts
------------------------------------------------------------------------

-- | @'Lift' src tgt@ is an index-renaming environment that maps every
-- variable in scope @src@ to a variable in scope @tgt@.
--
-- Terminology follows substitution calculi:
--
--  * @'ElShft' σ k@ represents @σ ∘ ↑ᵏ@: add @k@ to the index, /then/ apply
--    @σ@. Note this means the inner lift must accept indices in @k + src@.
--  * @'ElLft'  k σ@ represents @⇑ᵏ(σ)@: apply @σ@ under @k@ binders.
--
-- __Invariant__: no 'ElLft' of 'ElId'; no two consecutive 'ElLft'; no two
-- consecutive 'ElShft'.
data Lift (src :: Nat) (tgt :: Nat) where
  -- | Identity: @Γ ⊢ ElId : Γ@
  ElId :: Lift n n
  -- | @σ ∘ ↑ᵏ@: add @k@ to the index then apply @σ@.
  ElShft :: Lift (k + src) tgt -> !(SNat k) -> Lift src tgt
  -- | @⇑ᵏ(σ)@: the first @k@ indices are fixed, the rest go through @σ@.
  ElLft :: !(SNat k) -> Lift src tgt -> Lift (k + src) (k + tgt)

elId :: Lift n n
elId = ElId

-- | Add a shift of magnitude @k@ on the outside.
elShftRec :: forall k src tgt. SNat k -> Lift (k + src) tgt -> Lift src tgt
elShftRec n (ElShft el (k :: SNat k'))
  | Refl <- axiomAssoc @k' @k @src =
      ElShft el (sPlus k n)
elShftRec n el = ElShft el n

elShft :: forall k src tgt. SNat k -> Lift (k + src) tgt -> Lift src tgt
elShft n el = case snat_ n of
  SZ_ -> el
  _ -> elShftRec n el

-- | Lift under @n@ additional binders.
elLiftnRec :: forall n src tgt. SNat n -> Lift src tgt -> Lift (n + src) (n + tgt)
elLiftnRec _ ElId = ElId
elLiftnRec n (ElLft (k :: SNat k) (el :: Lift s t))
  | Refl <- axiomAssoc @n @k @s,
    Refl <- axiomAssoc @n @k @t =
      ElLft (sPlus n k) el
elLiftnRec n el = ElLft n el

elLiftn :: forall n src tgt. SNat n -> Lift src tgt -> Lift (n + src) (n + tgt)
elLiftn n el = case snat_ n of
  SZ_ -> el
  _ -> elLiftnRec n el

-- | Lift under one additional binder.
elLift :: Lift src tgt -> Lift (S src) (S tgt)
elLift = elLiftnRec s1

-- | Relocate a well-scoped de Bruijn index through a 'Lift'.
relocRel :: forall src tgt. Fin src -> Lift src tgt -> Fin tgt
relocRel i ElId = i
relocRel i (ElShft el k) = relocRel (Fin.shiftN k i) el
relocRel i (ElLft (k :: SNat k) (el :: Lift s t)) =
  withSNat k $ case Fin.split @k @s i of
    Left j -> Fin.weakenFinRight (Proxy :: Proxy t) j
    Right j -> Fin.shiftN k (relocRel j el)

-- | Internal: relocate a raw 0-based integer index.
relocRelInt :: Int -> Lift s t -> Int
relocRelInt n ElId = n
relocRelInt n (ElShft el k) = relocRelInt (n + toInt k) el
relocRelInt n (ElLft k el)
  | n < toInt k = n
  | otherwise = relocRelInt (n - toInt k) el + toInt k

isLiftId :: Lift src tgt -> Bool
isLiftId ElId = True
isLiftId (ElShft e n) = toInt n == 0 && isLiftId e
isLiftId (ElLft _ e) = isLiftId e

------------------------------------------------------------------------
-- * Substitutions
------------------------------------------------------------------------

-- $doc
-- Substitutions are represented as skewed-list trees with shift annotations.
-- The intuitive (inefficient) form is:
--
-- > data NaiveSubs a = SNil | SCons (OrVar a) (NaiveSubs a) | SShift (NaiveSubs a)
--
-- The efficient form groups shifts as tree-node annotations and uses skewed
-- binary trees for O(log n) access.

-- | Accumulated shift annotation.
type Shf = SNat

cmpShf :: Shf n -> Shf m -> Shf (n + m)
cmpShf = sPlus

idnShf :: Shf N0
idnShf = SZ

-- | A substitution slot: a concrete value, or a variable of the base scope.
--
-- Both are relative to the /base/ scope of the enclosing tree; the accumulated
-- shift on the path from the root must still be applied.
data OrVar a (m :: Nat)
  = Arg (a m)
  | Var (Fin m)

deriving instance (Show (a m)) => Show (OrVar a m)

deriving instance (Eq (a m)) => Eq (OrVar a m)

-- | A complete skewed binary tree storing @S w@ entries.
--
-- A tree is a /sequence/ of entries: the root's entry comes first, then the
-- entries of the left subtree, then those of the right subtree. Each node
-- records a shift @k@ applying to everything underneath it, and caches the
-- combined shift of its two subtrees. Because the entries are sequenced, the
-- base scope of the left subtree is the range of the right subtree.
data Tree a (w :: Nat) (k :: Nat) (m :: Nat) where
  Leaf :: SNat k -> OrVar a m -> Tree a Z k m
  Node ::
    -- | local shift amount for this node
    SNat k ->
    OrVar a (k1 + (k2 + m)) ->
    -- | size index of each subtree
    SNat w ->
    Tree a w k1 (k2 + m) ->
    Tree a w k2 m ->
    -- | cached @evalTree left + evalTree right@
    SNat (k1 + k2) ->
    Tree a (S (w + S w)) (k + (k1 + k2)) m

-- | A substitution as a skewed list of trees, covering exactly @n@ variables.
--
-- @'Nil' w sz@ is the identity on @sz@ variables, shifted by @w@; @'Cons' w t
-- rest@ prefixes a tree of @S w@ entries.
data Subs a (n :: Nat) (p :: Nat) where
  Nil :: SNat w -> SNat n -> Subs a n (w + n)
  Cons :: SNat w -> Tree a w k m -> Subs a n m -> Subs a (S (w + n)) (k + m)

-- | Total accumulated shift stored in a tree. Constant time: it is cached at
-- every node.
evalTree :: Tree a w k m -> SNat k
evalTree (Leaf w _) = w
evalTree (Node w1 _ _ _ _ w2) = cmpShf w1 w2

-- | Smart constructors with zero initial shift.
mkLeaf :: OrVar a m -> Tree a Z Z m
mkLeaf = Leaf idnShf

mkNode ::
  SNat w ->
  Tree a w k1 (k2 + m) ->
  OrVar a (k1 + (k2 + m)) ->
  Tree a w k2 m ->
  Tree a (S (w + S w)) (k1 + k2) m
mkNode w t1 x t2 = Node idnShf x w t1 t2 (cmpShf (evalTree t1) (evalTree t2))

------------------------------------------------------------------------
-- Lookup
------------------------------------------------------------------------

-- | An entry of a substitution together with the shift that still has to be
-- applied to it: the entry lives in scope @b@, and shifting it by @s@ lands it
-- in scope @p@.
data Shifted a (p :: Nat) where
  Shifted :: SNat s -> OrVar a b -> Shifted a (s + b)

-- | Look up the @i@-th entry of a tree, under an accumulated shift of @acc@.
treeGet ::
  forall acc a w k m.
  SNat acc ->
  Tree a w k m ->
  Fin (S w) ->
  Shifted a (acc + (k + m))
treeGet acc t i =
  case t of
    Leaf (k :: SNat k0) (x :: OrVar a m0)
      | Refl <- axiomAssoc @acc @k0 @m0 ->
          case i of
            FZ -> Shifted (cmpShf acc k) x
            FS j -> case j of {}
    Node
      (k :: SNat k0)
      (x :: OrVar a (k1 + (k2 + m0)))
      (w :: SNat w0)
      (t1 :: Tree a w0 k1 (k2 + m0))
      (t2 :: Tree a w0 k2 m0)
      _
        | Refl <- axiomAssoc @k1 @k2 @m0,
          Refl <- axiomAssoc @k0 @(k1 + k2) @m0,
          Refl <- axiomAssoc @acc @k0 @(k1 + (k2 + m0)),
          Refl <- axiomAssoc @(acc + k0) @k1 @(k2 + m0) ->
            case i of
              FZ -> Shifted (cmpShf acc k) x
              FS j -> withSNat (next w) $ case Fin.split @(S w0) @(S w0) j of
                Left j0 -> treeGet (cmpShf acc k) t1 j0
                Right j0 -> treeGet (cmpShf (cmpShf acc k) (evalTree t1)) t2 j0

-- | Look up index @i@ in a substitution, under an accumulated shift of @acc@.
--
-- Unlike the Rocq original there is no \"out of domain\" result: a @'Fin' n@
-- cannot exceed the domain of a @'Subs' a n p@.
getAux :: forall acc a n m. SNat acc -> Subs a n m -> Fin n -> Shifted a (acc + m)
getAux acc s i =
  case s of
    Nil (w :: SNat w) _
      | Refl <- axiomAssoc @acc @w @n ->
          Shifted (cmpShf acc w) (Var i)
    Cons (w :: SNat w) (t :: Tree a w k m1) (rest :: Subs a n2 m1)
      | Refl <- axiomAssoc @acc @k @m1 ->
          withSNat (next w) $ case Fin.split @(S w) @n2 i of
            Left j -> treeGet acc t j
            Right j -> getAux (cmpShf acc (evalTree t)) rest j

-- | Look up a well-scoped index in a substitution.
getSubs :: Fin n -> Subs a n m -> Shifted a m
getSubs i s = getAux idnShf s i

-- | The result of expanding a variable through a substitution.
data Expansion a (p :: Nat) where
  -- | Maps to the value @v@, which lives in scope @b@; shift it by @s@.
  EArg :: SNat s -> a b -> Expansion a (s + b)
  -- | Maps to a variable of the codomain.
  EVar :: Fin p -> Expansion a p

-- | Expand a well-scoped de Bruijn index in a substitution.
expandRel :: Fin n -> Subs a n m -> Expansion a m
expandRel i s = case getSubs i s of
  Shifted k (Arg v) -> EArg k v
  Shifted k (Var j) -> EVar (Fin.shiftN k j)

------------------------------------------------------------------------
-- Construction and modification
------------------------------------------------------------------------

-- | Add a shift annotation to the front of a tree. Constant time.
treeWrite :: forall p a w k m. Shf p -> Tree a w k m -> Tree a w (p + k) m
treeWrite p (Leaf k x) = Leaf (cmpShf p k) x
treeWrite
  p
  ( Node
      (k :: SNat k0)
      x
      (w :: SNat w0)
      (t1 :: Tree a w0 k1 (k2 + m))
      (t2 :: Tree a w0 k2 m)
      kt
    )
    | Refl <- axiomAssoc @p @k0 @(k1 + k2) =
        Node (cmpShf p k) x w t1 t2 kt

-- | Add a shift annotation to the front of a substitution. Constant time.
writeShf :: forall p a n m. Shf p -> Subs a n m -> Subs a n (p + m)
writeShf p (Nil (w :: SNat w) (sz :: SNat n))
  | Refl <- axiomAssoc @p @w @n =
      Nil (cmpShf p w) sz
writeShf p (Cons (w :: SNat w) (t :: Tree a w k m1) rest)
  | Refl <- axiomAssoc @p @k @m1 =
      Cons w (treeWrite p t) rest

-- | Prepend an 'OrVar' entry, merging the two leading trees when they have the
-- same size, which is what keeps the list skew-binary (and lookup logarithmic).
consOrVar :: forall a n m. OrVar a m -> Subs a n m -> Subs a (S n) m
consOrVar
  x
  ( Cons
      (w1 :: SNat w1)
      (l :: Tree a w1 k1 m1)
      (Cons (w2 :: SNat w2) (r :: Tree a w2 k2 m2) (rest :: Subs a n3 m2))
    )
    | Just Refl <- testEquality w1 w2,
      Refl <- axiomAssoc @k1 @k2 @m2,
      Refl <- axiomAssoc @w1 @(S w1) @n3 =
        Cons (next (sPlus w1 (next w1))) (mkNode w1 l x r) rest
consOrVar x s = Cons SZ (mkLeaf x) s

-- | Prepend a concrete value.
subsCons :: a m -> Subs a n m -> Subs a (S n) m
subsCons v = consOrVar (Arg v)

-- | The identity substitution for @n@ variables (no shift).
subsId :: SNat n -> Subs a n n
subsId = Nil idnShf

isSubsId :: Subs a n m -> Bool
isSubsId (Nil w _) = toInt w == 0
isSubsId _ = False

-- | Apply a shift of @k@ to the whole substitution.
subsShft :: Shf k -> Subs a n p -> Subs a n (k + p)
subsShft = writeShf

-- | Lift a substitution under one additional binder.
subsLift :: forall a n m. Subs a n m -> Subs a (S n) (S m)
subsLift (Nil (snat_ -> SZ_) sz) = Nil idnShf (next sz)
subsLift s = consOrVar (Var FZ) (writeShf s1 s)

-- | Lift a substitution under @k@ additional binders.
subsLiftn :: forall k a n m. SNat k -> Subs a n m -> Subs a (k + n) (k + m)
subsLiftn k (Nil (snat_ -> SZ_) sz) = Nil idnShf (sPlus k sz)
subsLiftn k s = case snat_ k of
  SZ_ -> s
  SS_ k' -> subsLift (subsLiftn k' s)

------------------------------------------------------------------------
-- Applying a 'Lift' to a substitution entry
------------------------------------------------------------------------

-- | Apply a lift to an 'OrVar', using @mk@ for concrete values.
applyLift ::
  (forall s t. Lift s t -> a s -> a t) ->
  Lift m p ->
  OrVar a m ->
  OrVar a p
applyLift _ e (Var i) = Var (relocRel i e)
applyLift mk e (Arg v) = Arg (mk e v)

------------------------------------------------------------------------
-- * Internal / diagnostic utilities
------------------------------------------------------------------------

-- | A more intuitive representation for weakenings.
--
-- Unlike 'Lift' (which uses @σ ↦ ↑ⁿ ∘ σ@), 'Weakening' uses
-- @σ ↦ σ ∘ ↑ⁿ@ ('WkWeak'), reversing the direction.
data Weakening
  = WkId
  | -- | @⇑ⁿ(σ)@: under @n@ binders
    WkLift Int Weakening
  | -- | @σ ∘ ↑ⁿ@: weaken by @n@
    WkWeak Int Weakening
  deriving (Eq, Show)

wkWeak :: Int -> Weakening -> Weakening
wkWeak n (WkWeak k w) = WkWeak (k + n) w
wkWeak n w = WkWeak n w

weak :: Int -> Weakening -> Weakening
weak 0 w = w
weak n w = wkWeak n w

wkLift :: Int -> Weakening -> Weakening
wkLift _ WkId = WkId
wkLift n (WkLift k w) = WkLift (n + k) w
wkLift n w = WkLift n w

liftW :: Int -> Weakening -> Weakening
liftW 0 w = w
liftW n w = wkLift n w

-- | Convert a 'Lift' to the 'Weakening' representation.
weakeningOfLift :: Lift src tgt -> Weakening
weakeningOfLift = go 0
  where
    go :: forall s t. Int -> Lift s t -> Weakening
    go _ ElId = WkId
    go pending (ElShft el k) = weak (toInt k) (go (pending + toInt k) el)
    go pending (ElLft k el)
      | toInt k > pending = liftW (toInt k - pending) (go 0 el)
      | otherwise = go (pending - toInt k) el

ppWeakeningAux :: Weakening -> String
ppWeakeningAux WkId = "keep..]"
ppWeakeningAux (WkLift k w) = "keep " ++ show k ++ "; " ++ ppWeakeningAux w
ppWeakeningAux (WkWeak k w) = "drop " ++ show k ++ "; " ++ ppWeakeningAux w

ppWeakening :: Weakening -> String
ppWeakening w = "[" ++ ppWeakeningAux w

ppLift :: Lift src tgt -> String
ppLift = ppWeakening . weakeningOfLift

-- | A substitution entry: a relocated variable or a value with its shift.
data OrRel a where
  -- | a variable, with the shift already applied
  Rel :: Int -> OrRel a
  -- | a value, with the shift still to apply
  Val :: Int -> a m -> OrRel a

toRel :: Int -> OrVar a m -> OrRel a
toRel shift (Var i) = Rel (toInt i + shift)
toRel shift (Arg v) = Val shift v

getTreeSubst :: Int -> [OrRel a] -> Tree a w k m -> [OrRel a]
getTreeSubst shift accu (Leaf w x) =
  toRel (shift + toInt w) x : accu
getTreeSubst shift accu (Node w x _ l r _) =
  let accu1 = getTreeSubst (shift + toInt w + toInt (evalTree l)) accu r
      accu2 = getTreeSubst (shift + toInt w) accu1 l
   in toRel (shift + toInt w) x : accu2

getSubstList :: Int -> [OrRel a] -> Subs a n m -> [OrRel a]
getSubstList shift _ (Nil w sz) =
  map (\i -> Rel (toInt w + i + shift)) [0 .. toInt sz - 1]
getSubstList shift accu (Cons _ t s) =
  let accu' = getSubstList (shift + toInt (evalTree t)) accu s
   in getTreeSubst shift accu' t

getShiftTotal :: Int -> Subs a n m -> Int
getShiftTotal accu (Nil w sz) = accu + toInt w + toInt sz
getShiftTotal accu (Cons _ t s) = getShiftTotal (toInt (evalTree t) + accu) s

-- | Decompose a substitution into an explicit list of entries and a final shift.
repr :: Subs a n m -> ([OrRel a], Int)
repr s = (getSubstList 0 [] s, getShiftTotal 0 s)
