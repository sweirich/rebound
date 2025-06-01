-- |
-- Module      : Data.Fin
-- Description : Bounded natural numbers
-- Stability   : experimental
--
-- This file re-exports definitions from fin's Data.Fin, while adding a few more
-- that are relevant to this context. Like Data.Fin, is meant to be used qualified.
--       import Fin (Fin (..))
--       import qualified Fin as Fin
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}
module Data.Fin(
  Nat(..), 
  SNat(SZ,SS),
  Fin,
  fs, Fin_(FZ_,FS_), fin_, Data.Fin.prev, 
  toNatural, toInteger, 
  mirror, 
  absurd,
  universe,
  f0,f1,f2,f3,
  invert,
  shiftN,
  shift1,
  weakenFin,
  weakenFinRight,
  weaken1Fin,
  weaken1FinRight,
  strengthen1Fin,
  strengthenRecFin,
 ) where


import Data.SNat hiding (succ)
import Data.Proxy (Proxy (..))
import GHC.Num.Natural (Natural)
import Test.QuickCheck
import Control.DeepSeq (NFData (..))

-- for efficiency
import Unsafe.Coerce(unsafeCoerce)

-------------------------------------------------------------------------------
-- Fin type
-------------------------------------------------------------------------------

newtype Fin (n :: Nat) = UnsafeFin Int
  deriving (NFData)
type role Fin nominal

toNatural :: Fin n -> Natural
toNatural (UnsafeFin x) = (fromInteger . toInteger) x

absurd :: Fin N0 -> a
absurd x = error "impossible"

instance Eq (Fin n) where
  UnsafeFin x == UnsafeFin y = x == y
instance Ord (Fin n) where
  compare (UnsafeFin x) (UnsafeFin y) = compare x y
instance Show (Fin n) where
  show (UnsafeFin x) = show x


fs :: Fin n -> Fin (S n)
fs (UnsafeFin x) = UnsafeFin (x + 1)

data Fin_ n where
  FZ_ :: Fin_ (S n)
  FS_ :: Fin n -> Fin_ (S n)

fin_ :: Fin n -> Fin_ n
fin_ (UnsafeFin 0) = unsafeCoerce FZ_
fin_ (UnsafeFin x) = unsafeCoerce $ FS_ (UnsafeFin (x-1))



-- FZ represents the "zero" element of Fin (S k)
pattern FZ :: forall (k :: Nat) . Fin (S k)
pattern FZ <- (UnsafeFin 0)  -- Matcher: succeeds if the wrapped Natural is 0
  where
    FZ = UnsafeFin 0      -- Constructor: creates UnsafeFin_ 0

-- Helper view function for the FS matcher
-- Takes the Natural value from a Fin (S k) and tries to find its predecessor's Natural value
viewFS :: Int -> Maybe (Fin k) -- The 'k' is inferred from the context of FS
viewFS currentNat
  | currentNat > 0 = 
    Just (UnsafeFin (currentNat - 1)) -- This will be wrapped as Fin k
  | otherwise      = Nothing -- Zero has no predecessor in this Fin model

-- FS m represents the "successor" of m.
-- If m :: Fin k, then FS m :: Fin (S k).
pattern FS :: forall (k :: Nat) (n :: Nat). Fin k -> Fin (S k)
pattern FS prevFin <- UnsafeFin (viewFS -> Just prevFin) -- Matcher
  where
    FS (UnsafeFin prevNat) = UnsafeFin (prevNat + 1)    -- Constructor

{-# COMPLETE FZ, FS :: Fin #-}

prev :: Fin (S k) -> Maybe (Fin k)
prev (UnsafeFin 0) = Nothing
prev (UnsafeFin x) = Just (UnsafeFin (x-1))

-------------------------------------------------------------------------------
-- Enum, Bounded, Num instances
-------------------------------------------------------------------------------

bound :: forall n. SNatI n => Int
bound = snatToInt (snat @n)

-- >>> [minBound .. maxBound] :: [Fin N3]
-- [0,1,2]

-- list all numbers up to some size
-- >>> universe :: [Fin N3]
-- [0,1,2]

-- in reverse order
-- >>> map mirror universe :: [Fin N3]
-- [2,1,0]


-- >>> :t toInteger
-- toInteger :: Integral a => a -> Integer

-- The `toInteger` instance has an unnecessary 
-- type class constraint (NatI n) for Fin. So we 
-- also include this class for simple conversion.
instance ToInt (Fin n) where
  toInt :: Fin n -> Int
  toInt (UnsafeFin x) = x

-- >>> :info Fin

-- >>> ([minBound .. maxBound] :: [Fin (S Z)])
-- [0]

instance SNatI n => Bounded (Fin n) where
  minBound = UnsafeFin 0
  maxBound = UnsafeFin (bound @n - 1)

-- These definitions are partial: they call error if they 
-- would produce a result not in the range 0 <= k < n
instance SNatI n => Enum (Fin n) where
  succ (UnsafeFin k) | k+1 <= bound @n
     = UnsafeFin (1 + k)
                     | otherwise = error $ "Cannot succ " ++ show k
  pred (UnsafeFin k) | k == 0 = UnsafeFin 0
                     | otherwise = UnsafeFin (k - 1)
  toEnum i = fromInteger (toInteger i)

  fromEnum = toInt 


instance SNatI n => Num (Fin n) where
  !(UnsafeFin k1) + !(UnsafeFin k2) 
    | k1 + k2 < bound @n = UnsafeFin (k1 + k2)
    | otherwise = error "addition out of range"
  UnsafeFin k1 - UnsafeFin k2 
    | k1 >= k2
    = UnsafeFin (k1 - k2)
    | otherwise = error "subtraction out of range"
  UnsafeFin k1 * UnsafeFin k2 
    | k1 * k2 < bound @n = UnsafeFin (k1 * k2)
    | otherwise = error "multiplication out of range"
  abs x = x
  signum (UnsafeFin x) = if x == 0 then 0 else 1
  fromInteger i | i < 0 = error "fromInteger: negative number"
  fromInteger i = 
    let
        k = fromInteger i 
    in
    if k < bound @n then UnsafeFin k 
    else error $ "fromInteger: out of range" ++ show (snat @n)

-- | Convert an "index" Fin to a "level" Fin and vice versa
invert :: forall n. SNatI n => Fin n -> Fin n
invert f = maxBound - f

mirror :: forall n. SNatI n => Fin n -> Fin n
mirror = invert

universe :: forall n. SNatI n => [Fin n]
universe | snatToNatural (snat @n) > 0 
         = [minBound .. maxBound]
         | otherwise
         = []
  
-------------------------------------------------------------------------------
-- Shifting and weakening
-------------------------------------------------------------------------------

-- Weakening: Adding a new binding to the context without changing existing
-- indices. 
-- Shifting: Adjusting the indices of free variables within a term to 
-- reflect a new binding added to the context. 

-- Shifting functions add some specified amount to the given 
-- `Fin` value, also incrementing its type.

-- In this module, we call the same operation `shiftN` and give 
-- it a slightly more convenient interface.
-- >>> shiftN s1 (f1 :: Fin N2)
-- 2


-- increment by a fixed amount (on the left)
shiftN :: forall n m . SNat n -> Fin m -> Fin (n + m)
shiftN p (UnsafeFin f) = UnsafeFin (snatToInt p + f)

shift1 :: Fin m -> Fin (S m)
shift1 = shiftN s1

-- We could also include a dual function, which increments on the right
-- but we haven't needed that operation anywhere.

-------------------------------------------------------------------------------
-- Weakening
-------------------------------------------------------------------------------

-- Weakenening changes the bound of a nat-indexed type without changing 
-- its value.
-- These operations can either be defined for the n-ary case (as in Fin below)
-- or be defined in terms of a single-step operation.
-- However, both of these operations are identity functions

-- | weaken the bound of a Fin by an arbitrary amount
-- >>> weakenFin (Proxy :: Proxy N1) (f1 :: Fin N2) :: Fin N3
-- 1
weakenFin :: proxy m -> Fin n -> Fin (m + n)
weakenFin _ !(UnsafeFin f) = UnsafeFin f

-- | weaken the bound of a Fin by 1.
weaken1Fin :: Fin n -> Fin (S n)
weaken1Fin = weakenFin s1

-- | weaken the bound of of a Fin by an arbitrary amount on the right.
-- This is also an identity function
-- >>> weakenFinRight (s1 :: SNat N1) (f1 :: Fin N2) :: Fin N3
-- 1
weakenFinRight :: proxy m -> Fin n -> Fin (n + m)
weakenFinRight m !(UnsafeFin f) = UnsafeFin f

-- | weaken the bound of a Fin by 1.
weaken1FinRight :: Fin n -> Fin (n + N1)
weaken1FinRight = weakenFinRight s1

-------------------------------------------------------------------------------
-- Aliases
-------------------------------------------------------------------------------

-- Convenient names for fin values. These have polymorphic types so they 
-- will work in any scope. (These are also called fin0, fin1, fin2, etc
-- in Data.Fin)

f0 :: Fin (S n)
f0 = UnsafeFin 0
f1 :: Fin (S (S n))
f1 = UnsafeFin 1
f2 :: Fin (S (S (S n)))
f2 = UnsafeFin 2
f3 :: Fin (S (S (S (S n))))
f3 = UnsafeFin 3

-- >>> f3
-- 3

-------------------------------------------------------------------------------
-- Strengthening
-------------------------------------------------------------------------------

-- With strengthening, we make sure that variable f0 is not used, 
-- and we decrement all other indices by 1. This allows us to 
-- also decrement the scope by one.

--- >>> strengthen1Fin (f0 :: Fin (S N3)) :: Maybe (Fin N3)
-- Nothing

-- >>> strengthen1Fin (f1 :: Fin (S N3)) :: Maybe (Fin N3)
-- Just 0

-- >>> strengthen1Fin (f2 :: Fin (S N3)) :: Maybe (Fin N3)
-- Just 1

strengthen1Fin :: forall n. SNatI n => Fin (S n) -> Maybe (Fin n)
strengthen1Fin = strengthenRecFin s0 s1 snat

-- We implement strengthening with the following operation that 
-- generalizes the induction hypothesis, so that we can strengthen
-- in the middle of the scope. The scope of the Fin should have the form
-- k + (m + n)  

-- Indices in the middle part of the scope `m` are "strengthened" away.

--- >>> strengthenRecFin s1 s1 s2 (f1 :: Fin (N1 + N1 + N2)) :: Maybe (Fin (N1 + N2))
-- Nothing

-- Variables that are in the first part of the scope `k` (the ones that have 
-- most recently entered the context) do not change when strengthening.

--- >>> strengthenRecFin s1 s1 s2 (f0 :: Fin (N1 + N1 + N2)) 
-- Just 0

-- Variables in the last part of the scope `n` are decremented by strengthening

-- >>> strengthenRecFin s1 s1 s2 (f2 :: Fin (N1 + N1 + N2)) :: Maybe (Fin N3)
-- Just 1

-- >>> strengthenRecFin s1 s1 s2 (f3 :: Fin (N1 + N1 + N2)) :: Maybe (Fin N3)
-- Just 2

strengthenRecFin :: SNat k -> SNat m -> SNat n -> Fin (k + (m + n)) -> Maybe (Fin (k + n))
strengthenRecFin k m n (UnsafeFin x) 
  | x < snatToInt k = Just (UnsafeFin x)
  | x < snatToInt k + snatToInt m = Nothing 
  | otherwise = Just $ UnsafeFin (x - snatToInt m)

{-
strengthenRecFin :: SNat k -> SNat m -> SNat n -> Fin (k + (m + n)) -> Maybe (Fin (k + n))
strengthenRecFin (snat_ -> SZ_) (snat_ -> SZ_) n x = Just x  -- Base case: k = 0, m = 0
strengthenRecFin (snat_ -> SZ_) (snat_ -> SS_ m) n FZ = Nothing  
  -- Case: k = 0, m > 0, and x is in the `m` range
strengthenRecFin (snat_ -> SZ_) (snat_ -> SS_ m) n (FS x) = 
    strengthenRecFin SZ m n x 
strengthenRecFin (snat_ -> SS_ k) m n f0 = Just FZ  
  -- Case: x < k, leave it alone
strengthenRecFin (snat_ -> SS_ k) m n (FS x) = 
    FS <$> strengthenRecFin k m n x 
-}
