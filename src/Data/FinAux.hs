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
{-# LANGUAGE ViewPatterns #-}
module Data.FinAux(
  SNat(..),Nat(..),
  module Data.Fin,
  f0,f1,f2,
  shiftN,
  weakenFin,
  weakenFinRight,
  strengthenRecFin,
  strengthenFin'
 ) where

import Data.Nat 
import Data.SNat 
import Data.Fin hiding (cata)
import Data.Proxy (Proxy (..))

import Data.Type.Equality
import Test.QuickCheck

-- for efficient rescoping
import Unsafe.Coerce(unsafeCoerce)


-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

--deriving instance Eq (Fin n)

--deriving instance Ord (Fin n)

-- | 'Fin' is printed as 'Int'.
--instance Show (Fin n) where show = show . toInt

-- >>> :t toInteger
-- toInteger :: Integral a => a -> Integer

-- The `toInteger` instance has an unnecessary 
-- type class constraint.
instance ToInt (Fin n) where
  toInt :: Fin n -> Int
  toInt FZ = 0
  toInt (FS x) = 1 + toInt x

{-
instance ToInt (Fin n) where
  
-}

-- >>> [minBound .. maxBound] :: [Fin N3]
-- [0,1,2]

-- list all numbers up to some size
-- >>> universe :: [Fin N3]
-- [0,1,2]

-------------------------------------------------------------------------------
-- Shifting
-------------------------------------------------------------------------------


-- These functions add the specified amount to the given 
-- `Fin`

-- In the Data.Fin libary, `weakenRight` changes the value of a Fin 
-- and its type. 

-- >>> :t weakenRight
-- weakenRight :: SNatI n => Proxy n -> Fin m -> Fin (Plus n m)

-- >>> weakenRight (Proxy :: Proxy N1) (f1 :: Fin N2) :: Fin N3
-- 2

-- Here, we call the same operation "shiftN"
-- >>> shiftN s1 (f1 :: Fin N2)
-- 2

-- increment by a fixed amount (on the left)
shiftN :: forall n m . SNat n -> Fin m -> Fin (n + m)
shiftN p f = withSNat p $ weakenRight (Proxy :: Proxy n) f

-- There is also a dual function, that increments on the right

-- >>> shiftRN s1 (f1 :: Fin N2)
-- 2

-- TODO: remove unsafeCoerce here
shiftRN :: forall m n. SNat m -> Fin n -> Fin (n + m)
shiftRN m n = undefined -- unsafeCoerce (shiftN m n)
-- shiftRN m = weakenLeft (Proxy :: Proxy m)

-- >>> shiftL @N2 @N2 @N1 s2 (FZ :: Fin N3)
-- 2

-- increment by a fixed amount
-- TODO: remove unsafeCoerce here
shiftL :: forall m1 m n. SNat m1 -> Fin (m + n) -> Fin ((m1 + m) + n)
shiftL m1 f = undefined -- unsafeCoerce (shiftN m1 f)

shiftR :: forall m m1 n. SNat m1 -> Fin (m + n) -> Fin ((m + m1) + n)
shiftR m1 f = undefined -- unsafeCoerce (shiftN m1 f)

-------------------------------------------------------------------------------
-- Weakening and Strengthening
-------------------------------------------------------------------------------

-- Weakenening and Strengthening change the bound of a nat-indexed type.
-- These operations can either be defined for the n-ary case (as in Fin below)
-- or be defined in terms of a single-step operation (though the latter is likely
-- to be inefficient.)
-- Both of these operations should be identity functions, so it would also be
-- justified to use unsafeCoerce.

-- In the Data.Fin library, weakenLeft does not change the value of a
-- Fin, it only changes its type.

-- >>> :t weakenLeft
-- weakenLeft :: SNatI n => Proxy m -> Fin n -> Fin (Plus n m)

-- >>> weakenLeft (Proxy :: Proxy N1) (f1 :: Fin N2) :: Fin N3
-- 1

-- >>> weaken1Fin f1
-- 1

weaken1Fin :: Fin n -> Fin (S n)
weaken1Fin = weakenFin s1

-- | weaken the bound of a Fin by an arbitrary amount
weakenFin :: proxy m -> Fin n -> Fin (m + n)
-- weakenFin m f = undefined -- withSNat m $ weakenLeft (Proxy :: Proxy m) f
weakenFin _ f = unsafeCoerce f

-- | weaken the bound of of a Fin by an arbitrary amount on the right
-- (I don't know why this is weakenLeft in the Data.Fin library. That 
-- is super confusing.)
weakenFinRight :: proxy m -> Fin n -> Fin (n + m)
weakenFinRight m f = unsafeCoerce f

{-
weakenFinRight SZ n =
  case axiomPlusZ @n of
    Refl -> n
weakenFinRight (SS (m :: SNat m1)) n =
  case axiom @n @m1 of
    Refl -> weaken1Fin (weakenFinRight m n)
-}

-- This is also an identity function
-- >>> weakenFinRight (s1 :: SNat N1) (f1 :: Fin N2)
-- 1


------------------------------------
{-
-- | compare bounded number f to see whether it is
-- less than p or not. If so, decrease bound. If not
-- return the ammount that it exceeds p
checkBound ::
  forall p n.
  SNat p ->
  Fin (p + n) ->
  Either (Fin p) (Fin n)
checkBound SZ = Right
checkBound (SS (p' :: SNat n2)) = \case
  FZ -> Left FZ
  (FS (f' :: Fin (n2 + n))) ->
    case checkBound @n2 @n p' f' of
      Left x -> Left (FS x)
      Right y -> Right y

pick :: Fin N2 -> a -> a -> a
pick f x y = case f of
  FZ -> x
  (FS _) -> y

-}
-------------------------------------------------------------------------------
-- Aliases
-------------------------------------------------------------------------------

f0 :: Fin (S n)
f1 :: Fin (S (S n))
f2 :: Fin (S (S (S n)))
f0 = FZ

f1 = FS f0

f2 = FS f1

-- >>> f2
-- 2

-- m = 1 , n = 3 , x = 2
-- >>> strengthenFin s1 s3 (f2 :: Fin (S N3)) :: Maybe (Fin N3)
-- Just 1
-- 

-- m = 1, n = 3, x = 0
--- >>> strengthenFin s1 s3 (f0 :: Fin (S N3)) :: Maybe (Fin N3)
-- Nothing

-- m = 1, n = 3, x = 3
--- >>> strengthenFin s1 s3 (FS f2 :: Fin (S N3)) :: Maybe (Fin N3)
-- Just 2

-- >>> strengthenFin' s1 s3 (f2 :: Fin (S N3)) :: Maybe (Fin N3)

-- update a reference so that it is valid for a smaller context
-- in other words, given 0 <= x < m + n,  if x >= m return x - m, otherwise return nothing

{-
strengthenFin :: forall m n. SNat m -> SNat n -> Fin (m + n) -> Maybe (Fin n)
strengthenFin SZ      n                    f      = Just f  -- (a)
strengthenFin (SS m)  n                    FZ     = Nothing -- (b)
strengthenFin (SS m0) SZ                   (FS f) = Nothing -- (c)
strengthenFin (SS m0) (SS (n0 :: SNat n0)) (FS f) = strengthenFin m0 (SS n0) f
-}
-- >>> strengthenRecFin SZ s1 s3 (f2 :: Fin (S N3)) :: Maybe (Fin N3)
-- Just 1

--- >>> strengthenRecFin SZ s1 s3 (f0 :: Fin (S N3)) :: Maybe (Fin N3)
-- Nothing

-- >>> strengthenRecFin SZ s1 s3 (FS f2 :: Fin (S N3)) :: Maybe (Fin N3)
-- Just 2

--- >>> strengthenRecFin s1 s1 s3 (f0 :: Fin (S (S N3))) 
-- Just 0

-- given 0 <= x < k + m + n, if x < k then leave alone, if k <= x < k+m return nothing, x >= k + m  return x - m
-- variables < k are left alone, variables k <= .. < k + m return Nothing, variables >= k + m shifted

strengthenRecFin :: SNat k -> SNat m -> SNat n -> Fin (k + (m + n)) -> Maybe (Fin (k + n))
strengthenRecFin SZ SZ n x = Just x  -- Base case: k = 0, m = 0
strengthenRecFin SZ (snat_ -> SS_ m) n FZ = Nothing  
  -- Case: k = 0, m > 0, and x is in the `m` range
strengthenRecFin SZ (snat_ -> SS_ m) n (FS x) = 
    strengthenRecFin SZ m n x 
strengthenRecFin (snat_ -> SS_ k) m n FZ = Just FZ  
  -- Case: x < k, leave it alone
strengthenRecFin (snat_ -> SS_ k) m n (FS x) = FS <$> strengthenRecFin k m n x 



  
{-  
  case (n,x) of 
  (n, FZ) -> case m of 
           SZ -> Just x    -- in k -- (a)
           SS _ -> Nothing  -- in m -- (b)
  (SZ,    FS f0) -> case m of  --
           SZ   -> Just x   -- in k
           SS _ -> Nothing  -- in m -- (c)
  (SS n0, FS (x0 :: Fin n0)) -> case m of 
              SZ -> Just x  -- x - m == x
              SS m0 -> _ where
                r = strengthenRecFin k m0 (SS n0) x0
-}

strengthenFin' :: SNat m -> SNat n -> Fin (m + n) -> Maybe (Fin n)
strengthenFin' = strengthenRecFin SZ

{-
strengthenFinRec k   SZ     n          FZ  = Just FZ
strengthenFinRec k   (SS m) n          FZ  = Nothing
strengthenFinRec SZ SZ SZ (FS f)  = Nothing
strengthenFinRec (SS (k :: SNat k)) SZ SZ (FS (f :: Fin n1)) = 
  case axiomPlusZ @k of Refl -> Just (FS f)
strengthenFinRec k   m      (SS n0) (FS f) = _
-}


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
invert n = withSNat n mirror
{-
invert (SS x) FZ = largest x
invert (SS x) (FS y) = weaken1Fin z where
  z = invert x y
invert SZ f = case f of {}
-}


-- convert a de Bruijn level (in scope n) to an
-- index in the same scope
--lvl2Idx :: forall n. Int -> SNat n -> Fin n
--lvl2Idx x l = toIdx l (sNat2Int l - x - 1)

{-
sNat2Int :: SNat n -> Int
sNat2Int SZ = 0
sNat2Int (SS n) = 1 + sNat2Int n

-- | ensure int is in bound
toIdx :: SNat n -> Int -> Fin n
toIdx (SS _n) 0 = FZ
toIdx (SS n) m | m > 0 = FS (toIdx n (m -1))
toIdx SZ _ = error "No indices in Ix Z"
toIdx _ _m = error "Negative index"
-}
