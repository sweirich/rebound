{-|
Module      : Tutorial.Scoped.Syntax
Description : Well-scoped abstract syntax for a simply-typed lambda calculus
              with nested pattern matching

-}
module Tutorial.Scoped.Syntax(
    Ty(..), Tm(..), Branch(..), Pat(..),Bind1,BindP,instantiate1,
    module Rebound,
    module Pat,
    ex_id, ex_const, ex_comp, ex_swap) where

import Rebound hiding (Ctx)
import Rebound.Bind.Pat as Pat
import Data.Maybe as Maybe
import Data.Fin

data Ty = One | Ty :-> Ty | Ty :* Ty | Ty :+ Ty
  deriving (Eq, Show)

data Tm (n :: Nat) where
    Var   :: Fin n -> Tm n
    Lam   :: Bind1 n -> Tm n
    Unit  :: Tm n
    Pair  :: Tm n -> Tm n -> Tm n
    Inj   :: Int -> Tm n -> Tm n
    App   :: Tm n -> Tm n -> Tm n
    Match :: Tm n -> [Branch n] -> Tm n
      deriving (Eq, Show)

data Branch (n :: Nat) where
    Branch :: BindP m n -> Branch n

-- m is the number of variables *bound* by the pattern
data Pat (m :: Nat) where
    PVar  :: LocalName -> Pat N1
    PUnit :: Pat N0
    PPair :: Pat m1 -> Pat m2 -> Pat (m2 + m1)
    PInj  :: Int -> Pat m -> Pat m


-- type abbreviations for convenience
type Bind1 n = Bind Tm Tm LocalName n
type BindP m n = Bind Tm Tm (Pat m) n

-- API operations for these types are instances of the general
-- operations in Rebound.Bind.Pat

bind1 :: LocalName -> Tm (S n) -> Bind1 n
bind1 = bind

getPat1 :: Bind1 n -> LocalName
getPat1 = getPat

getBody1 :: Bind1 n -> Tm (S n)
getBody1 = getBody

instantiate1 :: Bind1 n -> Tm n -> Tm n
instantiate1 b t = instantiate b (t .: zeroE) 

bindP :: Pat m -> Tm (m + n) -> BindP m n
bindP = bind

getPatP :: BindP m n -> Pat m
getPatP = getPat

getBodyP :: BindP m n -> Tm (m + n)
getBodyP = getBody

instantiateP :: BindP m n -> Env Tm m n -> Tm n
instantiateP = instantiate

--------------------------------------------------------------------
-- Example terms
--------------------------------------------------------------------

p1 :: Pat N1
p1 = PPair (PVar (LocalName "x")) (PInj 0 PUnit)

t1 :: Tm N0
t1 = Match Unit [Branch (bind p1 (Var f0))]

--- >>> p1



--- >>> t1



-- >>> Lam (bind (LocalName "x") (Var f0))




------------------------------------------------------------------------
-- * Examples
------------------------------------------------------------------------

-- | Identity function: λx. x  or  λ.0
ex_id :: Tm Z
ex_id = Lam (bind (LocalName "x") (Var f0))

-- | Constant function: λx. λy. x or λ.λ.1
ex_const :: Tm Z
ex_const = Lam (bind (LocalName "x") (Lam (bind (LocalName "y") (Var f1))))

-- | Function composition: λf. λg. λx. f (g x) or λ.λ.λ. 2 (1 0)
ex_comp :: Tm Z
ex_comp = Lam (bind (LocalName "f") (Lam (bind (LocalName "g") (Lam (bind (LocalName "x")
    (App (Var f2) (App (Var f1) (Var f0))))))))

-- | Swap a pair: λp. case p of (x, y) → (y, x)  or  λ. case 0 of (,) -> (0,1)
ex_swap :: Tm Z
ex_swap = Lam (bind (LocalName "p")
    (Match (Var f0)
        [ Branch (bind (PPair (PVar (LocalName "x")) (PVar (LocalName "y"))) 
                           (Pair (Var f0) (Var f1))) ]))


--------------------------------------------------------------------
-- Substitution
--------------------------------------------------------------------

instance SubstVar Tm where
  var :: Fin n -> Tm n
  var = Var
instance Subst Tm Tm where
  applyE :: Env Tm n m -> Tm n -> Tm m
  applyE r (Var x) = applyEnv r x
  applyE r (App e1 e2) = App (applyE r e1) (applyE r e2)
  applyE r (Lam b) = Lam (applyE r b)
  applyE r Unit = Unit
  applyE r (Pair e1 e2) = Pair (applyE r e1) (applyE r e2)
  applyE r (Inj i e) = Inj i (applyE r e)
  applyE r (Match e brs) = Match (applyE r e) (map (applyE r) brs)
instance Subst Tm Branch where
  applyE :: Env Tm n m -> Branch n -> Branch m
  applyE r (Branch b) = Branch (applyE r b)

-- >>> applyE (Unit .: zeroE) (Var FZ)



-- >>> applyE (Unit .: zeroE) (Lam (bind1 (LocalName "x") (Var f1)))



--------------------------------------------------------------------
-- Sized instance (counting bound variables)
--------------------------------------------------------------------

-- Any type that is used as a pattern must be an
-- instance of the `Sized` type class, so that the library
-- can determine the number of binding variables both
-- statically and dynamically.

-- The `Pat` type tells us how many variables are bound
-- the pattern with the index `n`. We can also recover
-- that number from the pattern itself by counting the number
-- of occurrences of `PVar`.

instance Sized (Pat m) where
    type Size (Pat m) = m

    size :: Pat m -> SNat (Size (Pat m))
    size (PVar _) = s1
    size PUnit = s0
    size (PPair p1 p2) = sPlus (size p2) (size p1)
    size (PInj _ p) = size p

-- >>> :t s1

-- >>> :t s0


-- The type `SNat` and type class `SNatI` provide *runtime* access to 
-- type-level natural numbers. Haskell is not a full-spectrum 
-- dependently-typed language, so numbers that appear in types cannot 
-- be pattern matched at runtime.

-- data SNat n where
--    SZ :: SNat Z
--    SS :: SNatI n1 => SNat (S n1)

-- The `SNatI n` acts as an implicit argument, and uses Haskell's type inference
-- to automatically supply runtime naturals when possible. The operations `snat`
-- and `withSNat` convert between implicit and explicit arguments.

-- >>> :t snat
-- snat :: SNatI n => SNat n

-- >>> :t withSNat
-- withSNat :: SNat n -> (SNatI n => r) -> r


-- There are singleton versions of various operations for 
-- natural numbers.  For example, we can add them:
-- >>> :t sPlus
-- sPlus :: SNat n1 -> SNat n2 -> SNat (n1 + n2)

-- We can also test them for equality. The (overloaded) 
-- `testEquality` operation has a heterogenous type and 
-- produces a proof of equivalence for its *indices* when its 
-- arguments are equal.

-- >>> :t testEquality @SNat
-- testEquality @SNat :: TestEquality SNat => SNat a -> SNat b -> Maybe (a :~: b)


--------------------------------------------------------------------
-- Alpha-equivalence 
--------------------------------------------------------------------

-- Two branches are equal when their patterns are equal and their 
-- bodies are equal
instance Eq (Branch n) where
  (==) :: Branch n -> Branch n -> Bool
  Branch b1 == Branch b2 = 
      case testEquality (getPat b1) (getPat b2) of
        Just Refl -> getBody b1 == getBody b2
        Nothing -> False

-- Compare two patterns for equality, even if we don't statically know 
-- that they bind the same number of variables.
instance TestEquality Pat where
  testEquality :: Pat a -> Pat b -> Maybe (a :~: b)
  testEquality (PPair p1 p2) (PPair p1' p2') = do
    Refl <- testEquality p1 p1'
    Refl <- testEquality p2 p2'
    return Refl
  testEquality (PVar x) (PVar y) = return Refl
  testEquality PUnit PUnit = return Refl
  testEquality (PInj i p) (PInj j p') | i == j = testEquality p p'
  testEquality _ _ = Nothing

instance (Eq (Pat m)) where
  (==) :: Pat m -> Pat m -> Bool
  p1 == p2 = Maybe.isJust (testEquality p1 p2)


--------------------------------------------------------------------
-- Show instances for Bind1 and Pat.Bind
--------------------------------------------------------------------

instance (Show p, Sized p) => Show (Pat.Bind Tm Tm p n) where
   showsPrec p bnd = 
      showParen (p > 10) $ 
      showString "bind " 
         . showsPrec 11 (Pat.getPat bnd) 
         . showString " " . showsPrec 11 (Pat.getBody bnd)

deriving instance (Show (Branch n))
deriving instance (Show (Pat m))
