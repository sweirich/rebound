
------------------------------------------------------------------------
--  Part III: Using the rebound library, and reflections
------------------------------------------------------------------------

module Talks.Hs26.Talk3 where

-- Import rebound library
import Rebound hiding (Ctx)
import Rebound.Bind.Pat qualified as Rebound (Bind)
import Rebound.Bind.Pat ( bind, getBody, getPat, instantiate )


------------------------------------------------------------------------
-- * Challenge: Lang where # of binding vars not statically known
------------------------------------------------------------------------
{-

-- lambda calculus with unit, products, and pattern matching
e ::= x | \ x . e | e1 e2 
   | () | (e1,e2) | inj1 e | inj2 e   
   | case e of { brs }                

-- list of branches
brs ::=   {- empty -}  |  p -> e ; brs    

-- pattern
p ::= x | () | (p1,p2) | inj1 p

-}

------------------------------------------------------------------------
-- * Syntax and binding specification
------------------------------------------------------------------------

-- rebound exports abstract `Bind` type 
-- Binds `n` variables of type `Tm` in body of type `Tm`, using pattern `p`
type Bind p n = Rebound.Bind Tm Tm p n

data Tm n = Var (Fin n) | Lam (Bind (SNat N1) n) | App (Tm n) (Tm n)  
   | Unit | Pair (Tm n) (Tm n) | Inj Int (Tm n)   
   | Match (Tm n) (BranchList n)
     deriving (Generic1)

-- A list of pattern bindings (BindP) of m variables, in scope n
-- BindP m n contains a pattern (Pat m) and body (Tm (m + n))
data BranchList (n :: Nat) where
    BNil  :: BranchList n
    BCons :: Bind (Pat m) n -> BranchList n -> BranchList n
      
-- A pattern: m is the number of variables *bound* by the pattern
-- A LocalName records a user-supplied name
data Pat (m :: Nat) where
    PVar  :: Pat N1                               -- x
    PUnit :: Pat N0                               -- ()
    PPair :: Pat m1 -> Pat m2 -> Pat (m2 + m1)    -- (p1, p2)
    PInj  :: Int -> Pat m -> Pat m                -- inj1 p / inj2 p


-----------------------------------------------------------------
-- API operations for Bind
-----------------------------------------------------------------

-- >>> :t bind

-- >>> :t getPat

-- Any type that is used as a pattern *must* be an
-- instance of the `Sized` type class, so that the library
-- can determine the number of binding variables.

-- >>> :t getBody

-- >>> :t instantiate

instantiate1 :: (Sized p, Size p ~ N1) => Bind p n -> Tm n -> Tm n
instantiate1 b t = instantiate b (t .: zeroE) 

--------------------------------------------------------------------
-- Sized instance (counting bound variables)
--------------------------------------------------------------------

instance Sized (Pat m) where
    type Size (Pat m)  = m

    size :: Pat m -> SNat (Size (Pat m))
    size PVar          = s1
    size PUnit         = s0
    size (PPair p1 p2) = sPlus (size p2) (size p1)
    size (PInj _ p)    = size p





--------------------------------------------------------------------
-- * Environments 
--------------------------------------------------------------------

-- Rebound exports an environment type:  `Env v m n` 
-- where
--     applyEnv :: Env v m n -> Fin m -> v n

-- >>> :t zeroE

-- >>> :t (.:)

-- Some operations need to identify "Var" constructor

-- >>> :t idE

-- >>> :t up

instance SubstVar Tm where
  var :: Fin n -> Tm n
  var = Var


--------------------------------------------------------------------
-- * Substitution
--------------------------------------------------------------------

-- applyE is a member multiparameter type class "Subst v c"
--   v - type in RHS of environment
--   c - type that we are substituting into

-- >>> :t applyE

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


-----------------------------------------------------------------
-- * Why is Bind an abstract type?
-----------------------------------------------------------------

-- Can create instances for Subst (and other classes)
--    instance SubstVar v => Subst v (Bind v c p)

-- Simplifies other instances (see above)
-- Allows optimization: delay substitution at binders, allowing 
-- fused traversals


--------------------------------------------------------------------
-- * Generic Substitution (GHC.Generics)
--------------------------------------------------------------------

-- can use GHC.Generics by replacing applyE above with isVar

-- >>> :t isVar


------------------------------------------------------------------------
-- * Alpha-equivalence
------------------------------------------------------------------------
-- (==) is alpha-equivalence 

-- Tm is *not* a GADT, so we can derive Eq instance for it
deriving instance (Eq (Tm n))

-- But Eq for BranchList is more challenging, due to the existential
instance Eq (BranchList n) where
  (==) :: BranchList n -> BranchList n -> Bool
  BNil == BNil = True
  BCons b1 brs1 == BCons b2 brs2 = {- b1 == b2 && -} brs1 == brs2
  _ == _ = False


-- >>> :t BCons

-- >>> :t getPat

-- >>> :t getBody

-- >>> :t testEquality @Pat

-- Compare two patterns for equality, even if we don't statically know 
-- that they bind the same number of variables.
instance TestEquality Pat where
  testEquality :: Pat a -> Pat b -> Maybe (a :~: b)
  testEquality (PPair p1 p2) (PPair p1' p2') = do
    Refl <- testEquality p1 p1'
    Refl <- testEquality p2 p2'
    return Refl
  testEquality PVar  PVar  = return Refl
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
patternMatch PVar v      = return (s1, oneE v)
patternMatch PUnit Unit  = return (s0, zeroE)
patternMatch (PPair p1 p2) (Pair v1 v2) = do
    (m1, env1) <- patternMatch p1 v1   
    (m2, env2) <- patternMatch p2 v2  
    -- (.++) needs to know the length of env2, supply it implicitly using withSNat
    return (sPlus m2 m1, withSNat m2 $ env2 .++ env1)
patternMatch (PInj i p) (Inj j v) | i == j = patternMatch p v
patternMatch _ _ = Nothing


--------------------------------------------------------------------
-- * What works for in Haskell?
--------------------------------------------------------------------

--   Erasure is the default 
--      - Agda can use @0 annotations, but erasure must be requested
--      - Haskell is the opposite: singletons indicate non-erasure

--   Type soundness holds in presence of nontermination 
--      - Weirich et al. "A specification of Dependent Haskell", ICFP 2017
--      - Can add pragmas to Agda, but proving termination is challenging
--        when substitutions are delayed in binders

--   Constraint solver automatically applies equations in types
--      - Sjoeberg & Weirich. "Programming Up-to-congruence", POPL 2015

--   Industrial-strength language features, libraries, and compiler (GHC)
--      - deriving and GHC.Generics 
--      - QuickCheck
--      - Overlapping instances, MPTC + functional dependencies 

--------------------------------------------------------------------
-- * Conclusion: What have we learned about DTP from Haskell?
--------------------------------------------------------------------

-- Internal verification is a sweet spot  
--   + (:~:) type important even in this context
--   + proofs written in this style are similar to Agda 
--     (see Agda port in repository for more details)
--   
-- When external verification is required, GHC has "answers"
--   + type inference supports "extensional" equality
--   + more expressive coercion language for proofs would help
--   + a combined terms and types would require a separate mechanism 
--     for requesting runtime witnesses 






