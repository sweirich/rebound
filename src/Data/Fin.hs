-- |
-- Module      : Data.Fin
-- Description : Bounded natural numbers
-- Stability   : experimental
--
-- A data type of bounded natural numbers. The type `Fin (S n)` contains numbers
-- within the range [0 .. n]. The type `Fin 0` is empty.
--
-- By design, this module is similar to
--     https://hackage.haskell.org/package/fin-0.3.1/docs/Data-Fin.html
-- but simpler. Eventually, this file may be replaced by that module.
--
-- This module is designed to be imported as
--
--       import Fin (Fin (..))
--       import qualified Fin
module Data.Fin where

import Data.Type.Equality
import Data.Nat
import Test.QuickCheck
import Unsafe.Coerce (unsafeCoerce)

-- a property about addition
axiom :: forall m n. Plus m (S n) :~: S (Plus m n)
axiom = unsafeCoerce Refl

axiomPlusZ :: forall m. Plus m Z :~: m
axiomPlusZ = unsafeCoerce Refl

-- that property generalized to +m
axiomM :: forall m p n. Plus p (Plus m n) :~: Plus m (Plus p n)
axiomM = unsafeCoerce Refl

axiomAssoc :: forall p m n. Plus p (Plus m n) :~: Plus (Plus p m) n
axiomAssoc = unsafeCoerce Refl

axiomIncrInj :: forall p1 p2. (Plus p1 N1 ~ Plus p2 N1) => p1 :~: p2
axiomIncrInj = case (axiomM @p1 @N1 @N0, axiomPlusZ @p1, axiomM @p2 @N1 @N0, axiomPlusZ @p2) of 
  (Refl,Refl,Refl,Refl) -> Refl

-----------------------------------------------------
-- Type
-----------------------------------------------------
data Fin (n :: Nat) where
  FZ :: Fin (S n)
  FS :: Fin n -> Fin (S n)

-- | Fold 'Fin'
cata :: forall a n. a -> (a -> a) -> Fin n -> a
cata z f = go
  where
    go :: Fin m -> a
    go FZ = z
    go (FS n) = f (go n)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

deriving instance Eq (Fin n)

deriving instance Ord (Fin n)

-- | 'Fin' is printed as 'Int'.
instance Show (Fin n) where show = show . toInt

instance ToInt (Fin n) where
  toInt :: Fin n -> Int
  toInt FZ = 0
  toInt (FS x) = 1 + toInt x

-- >>> [minBound .. maxBound] :: [Fin Three]
-- [0,1,2]

instance (n ~ S m, SNatI m) => Bounded (Fin n) where
  minBound = FZ
  maxBound = largest snat

largest :: SNat n -> Fin (S n)
largest SZ = FZ
largest (SS n) = FS (largest n)

instance (SNatI n) => Enum (Fin n) where
  toEnum :: Int -> Fin n
  toEnum = aux (snat :: SNat n)
    where
      aux :: forall n. SNat n -> Int -> Fin n
      aux SZ _ = error "to large"
      aux (SS n) 0 = FZ
      aux (SS n) m = FS (aux n (m - 1))

  fromEnum :: Fin n -> Int
  fromEnum = toInt

instance (SNatI n) => Arbitrary (Fin n) where
  arbitrary :: Gen (Fin n)
  arbitrary = elements (enumFin snat)

-- list all numbers up to some size

-- >>> enumFin s3
-- [0,1,2]

enumFin :: SNat n -> [Fin n]
enumFin SZ = []
enumFin (SS n) = FZ : map FS (enumFin n)

universe :: (SNatI n) => [Fin n]
universe = enumFin snat

-------------------------------------------------------------------------------
-- Shifting
-------------------------------------------------------------------------------

-- These functions add the specified amount to the given 
-- `Fin`


-- >>> shiftN s1 (f1 :: Fin N2)
-- 2

-- increment by a fixed amount (on the left)
shiftN :: SNat m -> Fin n -> Fin (Plus m n)
shiftN SZ f = f
shiftN (SS n) f = FS (shiftN n f)

-- >>> shiftRN s1 (f1 :: Fin N2)
-- 2

-- TODO: remove unsafeCoerce here
shiftRN :: forall m n. SNat n -> Fin m -> Fin (Plus m n)
shiftRN m f = unsafeCoerce (shiftN m f)

-- >>> shiftL @N2 @N2 @N1 s2 (FZ :: Fin N3)
-- 2

-- increment by a fixed amount
-- TODO: remove unsafeCoerce here
shiftL :: forall m1 m n. SNat m1 -> Fin (Plus m n) -> Fin (Plus (Plus m1 m) n)
shiftL m1 f = unsafeCoerce (shiftN m1 f)

shiftR :: forall m m1 n. SNat m1 -> Fin (Plus m n) -> Fin (Plus (Plus m m1) n)
shiftR m1 f = unsafeCoerce (shiftN m1 f)

-------------------------------------------------------------------------------
-- Weakening and Strengthening
-------------------------------------------------------------------------------

-- Weakenening and Strengthening just change the bound of a nat-indexed type.
-- These operations can either be defined for the n-ary case (as in Fin below)
-- or be defined in terms of a single-step operation (though the latter is likely
-- to be inefficient.)
-- Both of these operations should be identity functions, so it would also be
-- justified to use unsafeCoerce.

-- >>> weaken1Fin f1
-- 1

-- | weaken the bound of a Fin by an arbitrary amount
weakenFin :: SNat m -> Fin n -> Fin (Plus m n)
weakenFin SZ f = f
weakenFin (SS m) FZ = FZ
weakenFin (SS (m :: SNat m0)) (FS (f :: Fin n0)) = case axiom @m0 @n0 of
  Refl -> FS (weakenFin (SS m) f)

weaken1Fin :: Fin n -> Fin (S n)
weaken1Fin = weakenFin s1


-- | weaken the bound of of a Fin by an arbitrary amound on the right
weakenFinRight :: forall m n. SNat m -> Fin n -> Fin (Plus n m)
weakenFinRight SZ n =
  case axiomPlusZ @n of
    Refl -> n
weakenFinRight (SS (m :: SNat m1)) n =
  case axiom @n @m1 of
    Refl -> weaken1Fin (weakenFinRight m n)


-- This is also an identity function
-- >>> weakenFinRight (s1 :: SNat N1) (f1 :: Fin N2)
-- 1


------------------------------------

-- | compare bounded number f to see whether it is
-- less than p or not. If so, decrease bound. If not
-- return the ammount that it exceeds p
checkBound ::
  forall p n.
  SNat p ->
  Fin (Plus p n) ->
  Either (Fin p) (Fin n)
checkBound SZ = Right
checkBound (SS (p' :: SNat n2)) = \case
  FZ -> Left FZ
  (FS (f' :: Fin (Plus n2 n))) ->
    case checkBound @n2 @n p' f' of
      Left x -> Left (FS x)
      Right y -> Right y

pick :: Fin N2 -> a -> a -> a
pick f x y = case f of
  FZ -> x
  (FS _) -> y

-------------------------------------------------------------------------------
-- Aliases
-------------------------------------------------------------------------------

f0 :: Fin (S n)
f1 :: Fin (S (S n))
f2 :: Fin (S (S (S n)))
f0 = FZ

f1 = FS f0

f2 = FS f1



strengthenFin :: forall m n. SNat m -> SNat n -> Fin (Plus m n) -> Maybe (Fin n)
strengthenFin SZ SZ f = Just f
strengthenFin (SS m) SZ f = Nothing
strengthenFin m (SS n) FZ = Just FZ
strengthenFin m (SS (n0 :: SNat n0)) (FS f) =
  case axiom @m @n0 of
    Refl -> FS <$> strengthenFin m n0 f

-------------------------------------------------------------------------------
-- Invert
-------------------------------------------------------------------------------


-- >>> invert s3 f0
-- 2

-- >>> invert s3 f1
-- 1

-- >>> invert s3 f2
-- 0

invert :: SNat n -> Fin n -> Fin n
invert (SS x) FZ = largest x
invert (SS x) (FS y) = weaken1Fin z where
  z = invert x y
invert SZ f = case f of {}



-- convert a de Bruijn level (in scope n) to an
-- index in the same scope
lvl2Idx :: forall n. Int -> SNat n -> Fin n
lvl2Idx x l = toIdx l (sNat2Int l - x - 1)  

sNat2Int :: SNat n -> Int
sNat2Int SZ = 0
sNat2Int (SS n) = 1 + sNat2Int n

-- | ensure int is in bound
toIdx :: SNat n -> Int -> Fin n
toIdx (SS _n) 0 = FZ
toIdx (SS n) m | m > 0 = FS (toIdx n (m -1))
toIdx SZ _ = error "No indices in Ix Z"
toIdx _ _m = error "Negative index"
