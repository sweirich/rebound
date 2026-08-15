
------------------------------------------------------------------------
--  Part II: Using the rebound library
------------------------------------------------------------------------

module Talks.Hs26.Talk2 where

import Rebound hiding (Ctx)
import Rebound.Bind.Pat qualified as Rebound (Bind)
import Rebound.Bind.Pat ( bind, getBody, getPat, instantiate )


------------------------------------------------------------------------
-- * Let's add pattern matching
------------------------------------------------------------------------

{-

-- lambda calculus with unit, products, and pattern matching
e ::= x | \ x . e | e1 e2 
   | () | (e1,e2) | inj1 e | inj2 e   
   | case e of { brs }                


-- list of branches
brs ::=                 
     |  p -> e ; brs    

-- pattern
p ::= x | () | (p1,p2) | inj1 p

Key challenge: number of bound variables isn't known statically

-}

------------------------------------------------------------------------
-- * Syntax and binding specification
------------------------------------------------------------------------

-- rebound exports abstract `Bind` type 
-- Binds `n` variables of type `Tm` in body of type `Tm`, using pattern `p`
type Bind p n = Rebound.Bind Tm Tm p n

data Tm (n :: Nat) where
    Var   :: Fin n -> Tm n
    Lam   :: Bind LocalName n -> Tm n
    App   :: Tm n -> Tm n -> Tm n
    Unit  :: Tm n
    Pair  :: Tm n -> Tm n -> Tm n
    Inj   :: Int -> Tm n -> Tm n
    Match :: Tm n -> BranchList n -> Tm n
        deriving (Show, Eq, Generic1)

------------------------------------------------------------------------
-- * Pattern matching
------------------------------------------------------------------------ 

-- A list of pattern bindings (BindP) of m variables, in scope n
-- BindP m n contains a pattern (Pat m) and body (Tm (m + n))
data BranchList (n :: Nat) where
    BNil  :: BranchList n
    BCons :: Bind (Pat m) n -> BranchList n -> BranchList n
      
-- A pattern: m is the number of variables *bound* by the pattern
-- A LocalName records a user-supplied name
data Pat (m :: Nat) where
    PVar  :: LocalName -> Pat N1   -- remember user-supplied name
    PUnit :: Pat N0
    PPair :: Pat m1 -> Pat m2 -> Pat (m2 + m1)
    PInj  :: Int -> Pat m -> Pat m
      
-- BranchList has an existential and Pat is a GADT
-- Use standalone deriving for Show. 
-- But, have to do something else for Eq and Generic1
deriving instance (Show (BranchList n))
deriving instance (Show (Pat n))


-----------------------------------------------------------------
-- API operations for Bind
-----------------------------------------------------------------

-- >>> :t bind


-- >>> :t getPat


-- >>> :t getBody


-- >>> :t instantiate


instantiate1 :: Bind LocalName n -> Tm n -> Tm n
instantiate1 b t = instantiate b (t .: zeroE) 


--------------------------------------------------------------------
-- * Substitution 
--------------------------------------------------------------------

-- >>> :t var


-- >>> :t applyE


instance SubstVar Tm where
  var :: Fin n -> Tm n
  var = Var

instance Subst Tm Tm where
  applyE :: Env Tm n m -> Tm n -> Tm m
  applyE r (Var x)       = applyEnv r x
  applyE r (App e1 e2)   = App (applyE r e1) (applyE r e2)
  applyE r (Lam b)       = Lam (applyE r b)
  applyE r Unit          = Unit
  applyE r (Pair e1 e2)  = Pair (applyE r e1) (applyE r e2)
  applyE r (Inj i e)     = Inj i (applyE r e)
  applyE r (Match e brs) = Match (applyE r e) (applyE r brs)

instance Subst Tm BranchList where
  applyE :: Env Tm n m -> BranchList n -> BranchList m
  applyE r (BCons b brs) = BCons (applyE r b) (applyE r brs)
  applyE r BNil = BNil



--------------------------------------------------------------------
-- Sized instance (counting bound variables)
--------------------------------------------------------------------

-- Any type that is used as a pattern *must* be an
-- instance of the `Sized` type class, so that the library
-- can determine the number of binding variables both
-- *statically* and *dynamically*.

instance Sized (Pat m) where
    type Size (Pat m)  = m

    size :: Pat m -> SNat (Size (Pat m))
    size (PVar _)      = s1
    size PUnit         = s0
    size (PPair p1 p2) = sPlus (size p2) (size p1)
    size (PInj _ p)    = size p

-- >>> :t s1

-- >>> :t s0

-- >>> :t sPlus

--------------------------------------------------------------------

-- The type `SNat` and type class `SNatI` provide *runtime* access to 
-- type-level natural numbers. Haskell is not a full-spectrum 
-- dependently-typed language, so numbers that appear in types cannot 
-- be pattern matched at runtime.

-- data SNat n where
--    SZ :: SNat Z
--    SS :: SNatI n1 => SNat (S n1)

-- The `SNatI n` acts as an implicit argument and uses Haskell's 
-- type inference to automatically supply runtime naturals when 
-- possible. The operations `snat` and `withSNat` convert between 
-- implicit and explicit arguments.

--------------------------------------------------------------------
-- Alpha-equivalence 
--------------------------------------------------------------------

instance Eq (Pat m) where
  (==) :: Pat m -> Pat m -> Bool
  PVar n == PVar m = True
  PUnit == PUnit = True
  (PInj i p1) == (PInj j p2) = i == j && p1 == p2
  -- (PPair p1 p2) == (PPair p3 p4) = p1 == p3 && p2 == p4
  _ == _ = False

-- >>> :t testEquality @Pat

-- >>> s0 == s0
-- True

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


--------------------------------------------------------------------
-- Evaluator with pattern matching
--------------------------------------------------------------------


-- | (big-step) evaluation function
-- no scope errors, but types can fail at runtime
eval :: Tm Z -> Maybe (Tm Z)
eval (Var x)      = case x of {}
eval (Lam m)      = return (Lam m)
eval (App m n) = do
    mv <- eval m
    case mv of
      Lam b -> eval (instantiate1 b n) 
      _ -> Nothing
eval Unit         = return Unit
eval (Pair e1 e2) = do
    v1 <- eval e1
    v2 <- eval e2
    return (Pair v1 v2)
eval (Inj i m) = do
    t <- eval m
    return (Inj i t)
eval (Match e brs) = do
    v  <- eval e
    br <- findBranch v brs
    eval br

--------------------------------------------------------------------
-- Revised Evaluator, with pattern matching
--------------------------------------------------------------------

-- | Find the first branch whose pattern matches the scrutinee and
-- instantiate its body.
findBranch :: Tm Z -> BranchList Z -> Maybe (Tm Z)
findBranch _ BNil = Nothing
findBranch v (BCons b rest) =
    case patternMatch (getPat b) v of
        Just (_, r)  -> return (instantiate b r)
        Nothing -> findBranch v rest

-- | Compare a pattern against a value, returning an environment binding
-- the pattern variables (if the pattern matches)
patternMatch :: Pat m -> Tm Z -> Maybe (SNat m, Env Tm m Z)
patternMatch (PVar _) v  = return (s1, oneE v)
patternMatch PUnit Unit  = return (s0, zeroE)
patternMatch (PPair p1 p2) (Pair v1 v2) = do
    (m1, env1) <- patternMatch p1 v1   
    (m2, env2) <- patternMatch p2 v2  
    return (sPlus m2 m1, withSNat m2 $ env2 .++ env1)
patternMatch (PInj i p) (Inj j v) | i == j = patternMatch p v
patternMatch _ _ = Nothing


-- NOTE: the index m is static only. Environments don't store their 
-- domain, so we calculate it and make it implicitly available for .++


--------------------------------------------------------------------
-- * Equality is heterogenous and informative
--------------------------------------------------------------------
{-

Compare:

    (==) :: Pat a -> Pat a -> Bool

    testEquality :: Pat a -> Pat b -> Maybe (a :~: b)

Need to generalize type to define equivalence checking function.

If we know the patterns are equal, we also know they bind the 
same number of variables

-}


--------------------------------------------------------------------
-- * Proofs are sometimes possible
--------------------------------------------------------------------


{- Propositional equality in Haskell:

     data (:~:) a b where 
        Refl :: a :~: a

  - Good:
    
     * testEquality produces evidence of index
       equality during computation we need to do anyway
        - no cost for producing this evidence
        - GHC treats Refl as a "0-bit" value, so not cost to 
          pass it around

     * isVar returns evidence that var constructor is for 
       the right type

  - Not good: reasoning about the properties of arithmetic

     * assoc : forall x y z. (x + y) + z :~: x + (y + z)

-}


--------------------------------------------------------------------
-- * Singletons 
--------------------------------------------------------------------

{- From part 2:  singletons are needed (SNat), but minor

   Why did we need them?

   When the number of bound variables in a subterm is not statically 
   known.

   i.e. pattern matching can bind an arbitrary number of variables in 
   each branch.

-}


--------------------------------------------------------------------
-- Show instances for Pat.Bind
--------------------------------------------------------------------

-- | The show instance is for viewing the AST. 
instance (Show p, Sized p) => Show (Bind p n) where
   showsPrec p bnd = 
      showParen (p > 10) $ 
      showString "bind " 
         . showsPrec 11 (getPat bnd) 
         . showString " " . showsPrec 11 (getBody bnd)
