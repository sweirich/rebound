{-|

Part 2: Now let's see how rebound can help!  

In this module, we 
  - define the syntax, declaratively specifying binding structure
    including a *separate datatype* for patterns!
  - define capture avoiding substitution
  - define alpha-equivalence

NOTE: This module is an annotated version of Syntax.hs in the rebound Tutorial.

-}
module Tutorial.Talk2(
    Ty(..), Tm(..), BranchList(..), Pat(..),Bind1,BindP,instantiate1,
    module Rebound,
    module Pat) where

import Rebound hiding (Ctx)
import Rebound.Bind.Pat as Pat
import Data.Maybe as Maybe
import Data.Fin


------------------------------------------------------------------------
-- * Syntax and binding specification
------------------------------------------------------------------------

data Ty = One | Ty :-> Ty | Ty :* Ty | Ty :+ Ty
  deriving (Eq, Show)

data Tm (n :: Nat) where
    Var   :: Fin n -> Tm n
    Lam   :: Bind1 n -> Tm n
    Unit  :: Tm n
    Pair  :: Tm n -> Tm n -> Tm n
    Inj   :: Int -> Tm n -> Tm n
    App   :: Tm n -> Tm n -> Tm n
    Match :: Tm n -> BranchList n -> Tm n
      deriving (Eq, Show, Generic1)

-- A list of pattern bindings (BindP) of m variables, in scope n
-- BindP m n contains a pattern (Pat m) and body (Tm (m + n))
data BranchList (n :: Nat) where
    BNil :: BranchList n
    BCons :: BindP m n -> BranchList n -> BranchList n

-- A pattern: m is the number of variables *bound* by the pattern
-- A local name let's us record a user-supplied name
data Pat (m :: Nat) where
    PVar  :: LocalName -> Pat N1
    PUnit :: Pat N0
    PPair :: Pat m1 -> Pat m2 -> Pat (m2 + m1)
    PInj  :: Int -> Pat m -> Pat m

{-----------------------------------------------------------------}

-- API operations for these types are instances of the general
-- definitions and operations in Rebound.Bind.Pat

-- type abbreviations for convenience
type Bind1 n   = Bind Tm Tm LocalName n
type BindP m n = Bind Tm Tm (Pat m) n

-- Named, single binders

bind1 :: LocalName -> Tm (S n) -> Bind1 n
bind1 = bind

getPat1 :: Bind1 n -> LocalName
getPat1 = getPat

getBody1 :: Bind1 n -> Tm (S n)
getBody1 = getBody

instantiate1 :: Bind1 n -> Tm n -> Tm n
instantiate1 b t = instantiate b (t .: zeroE) 

-- patterns

bindP :: Pat m -> Tm (m + n) -> BindP m n
bindP = bind

getPatP :: BindP m n -> Pat m
getPatP = getPat

getBodyP :: BindP m n -> Tm (m + n)
getBodyP = getBody

instantiateP :: BindP m n -> Env Tm m n -> Tm n
instantiateP = instantiate

--------------------------------------------------------------------
-- * Substitution via type class instances
--------------------------------------------------------------------

-- >>> :t var


-- >>> :t applyE


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
  applyE r (Match e brs) = Match (applyE r e) (applyE r brs)
  

instance Subst Tm BranchList where
  applyE :: Env Tm n m -> BranchList n -> BranchList m
  applyE r (BCons b brs) = BCons (applyE r b) (applyE r brs)
  applyE r BNil = BNil

-- >>> applyE (Unit .: zeroE) (Var FZ)


-- >>> applyE (Unit .: zeroE) (Lam (bind1 (LocalName "x") (Var f1)))


--------------------------------------------------------------------
-- Sized instance (counting bound variables)
--------------------------------------------------------------------

-- Any type that is used as a pattern *must* be an
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

-- >>> :t sPlus
-- sPlus :: SNat n1 -> SNat n2 -> SNat (n1 + n2)


--------------------------------------------------------------------

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


--------------------------------------------------------------------
-- Alpha-equivalence 
--------------------------------------------------------------------

-- With dependent types, we sometimes need a heterogenously typed
-- equality operation for indexed types. The `testEquality` operation 
-- produces a proof of equivalence for its *indices* when its 
-- *arguments* are equal.

-- >>> :t testEquality @SNat

-- >>> s0 == s0

-- >>> s0 == s1

-- >>> testEquality s0 s1

-- >>> testEquality s0 s0


-- >>> :t BCons

-- Two branch list are equal when all patterns are equal and their 
-- bodies are equal
instance Eq (BranchList n) where
  (==) :: BranchList n -> BranchList n -> Bool
  BNil == BNil = True
  BCons b1 brs1 == BCons b2 brs2 = 
    case testEquality (getPat b1) (getPat b2) of
      Just Refl -> getBody b1 == getBody b2 && brs1 == brs2
      Nothing -> False
  _ == _ = False

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
-- Revised Evaluator, with pattern matching
--------------------------------------------------------------------

-- See Tutorial.Scoped.Eval









--------------------------------------------------------------------
-- Show instances for Pat.Bind
--------------------------------------------------------------------

-- | The show instance is for viewing the AST. We will also 
-- implement a pretty printer for a more convenient representation.

instance (Show p, Sized p) => Show (Pat.Bind Tm Tm p n) where
   showsPrec p bnd = 
      showParen (p > 10) $ 
      showString "bind " 
         . showsPrec 11 (Pat.getPat bnd) 
         . showString " " . showsPrec 11 (Pat.getBody bnd)

deriving instance (Show (BranchList n))
deriving instance (Show (Pat m))
