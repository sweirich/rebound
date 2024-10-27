module Vec where

-- Library for `Nat`, `Fin` and `Vec`, i.e. bounded natural numbers and length-indexed lists

import Data.Type.Equality
import Test.QuickCheck

-----------------------------------------------------
class ToInt n where
    toInt :: n -> Int

-----------------------------------------------------
-- Nats (and singleton nats and implicit singletons)
-----------------------------------------------------
data Nat = Z | S Nat
    deriving (Eq, Ord)

type One = S Z
type Two = S One
type Three = S Two 

zero :: Fin (S n)
zero = FZ

one :: Fin (S (S n))
one = FS FZ

two :: Fin (S (S (S n)))
two = FS (FS FZ)

data SNat (n :: Nat) where
    SZ :: SNat Z
    SS :: SNat n -> SNat (S n)

class SNatI (n :: Nat) where
    snat :: SNat n
instance SNatI Z where 
    snat :: SNat Z
    snat = SZ
instance SNatI n => SNatI (S n) where 
    snat :: SNatI n => SNat (S n)
    snat = SS snat

instance ToInt Nat where 
    toInt Z = 0
    toInt (S n) = 1 + toInt n
instance ToInt (SNat n) where
    toInt SZ = 0
    toInt (SS n) = 1 + toInt n

instance Show Nat where show = show . toInt
instance Show (SNat n) where show = show . toInt


instance TestEquality SNat where
    testEquality :: SNat a -> SNat b -> Maybe (a :~: b)
    testEquality SZ SZ = Just Refl
    testEquality (SS x) (SS y) 
       | Just Refl <- testEquality x y = Just Refl
    testEquality _ _ = Nothing

instance SNatI n => Arbitrary (SNat n) where
    arbitrary :: SNatI n => Gen (SNat n)
    arbitrary = pure snat

-----------------------------------------------------
-- Fins
-----------------------------------------------------
data Fin (n :: Nat) where
    FZ :: Fin (S n)
    FS :: Fin n -> Fin (S n)


instance ToInt (Fin n) where
   toInt :: Fin n -> Int
   toInt FZ = 0
   toInt (FS x) = 1 + toInt x
instance Show (Fin n) where show = show . toInt

-- list all numbers up to some size
enumFin :: SNat n -> [Fin n]
enumFin SZ = []
enumFin (SS n) = FZ : map FS (enumFin n)

-- increase the bound of a Fin.
-- this is an identity function 
weakenFin :: Fin n -> Fin (S n)
weakenFin FZ = FZ
weakenFin (FS f) = FS (weakenFin f)

instance SNatI n => Arbitrary (Fin n) where
    arbitrary :: Gen (Fin n)
    arbitrary = elements (enumFin snat)

deriving instance Eq (Fin n)
deriving instance Ord (Fin n)

instance Bounded (Fin One) where
    minBound = FZ
    maxBound = FZ

instance Bounded (Fin (S n)) => Bounded (Fin (S (S n))) where
    minBound = FZ
    maxBound = FS maxBound

instance SNatI n => Enum (Fin n) where
    toEnum :: Int -> Fin n
    toEnum = aux (snat :: SNat n) where
        aux :: forall n. SNat n -> Int -> Fin n
        aux SZ _ = error "to large"
        aux (SS n) 0 = FZ
        aux (SS n) m = FS (aux n (m - 1))

    fromEnum :: Fin n -> Int
    fromEnum = toInt

-- >>> enumFin (SS (SS (SS SZ)))
-- [0,1,2]

-- >>> [minBound .. maxBound] :: [Fin Three]
-- [0,1,2]


pick :: Fin Two -> a -> a -> a
pick f x y = case f of
    FZ -> x
    (FS _) -> y

-----------------------------------------------------
-- Vectors
-----------------------------------------------------

data Vec n a where
    Nil  :: Vec Z a
    Cons :: a -> Vec n a -> Vec (S n) a

deriving instance Functor (Vec n)
deriving instance Foldable (Vec n)
deriving instance Show a => Show (Vec n a)

data LE m n where
    LZ :: LE m m 
    LS :: LE m n -> LE m (S n)



shift :: LE m n -> Fin m -> Fin n
shift LZ f = f
shift (LS le) f = FS (shift le f) 


vlength :: Vec n a -> SNat n
vlength Nil = SZ
vlength (Cons _ vs) = SS (vlength vs)

lookupVec :: Fin n -> Vec n a -> a
lookupVec FZ (Cons v _)= v
lookupVec (FS v) (Cons _ env) = lookupVec v env

replaceVec :: Fin n -> Vec n a -> a -> Vec n a
replaceVec FZ (Cons _ vs) w = Cons w vs
replaceVec (FS x) (Cons w1 env) w2 = Cons w1 (replaceVec x env w2)
