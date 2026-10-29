------------------------------------------------------------------------
--  Part II: Using the rebound library, and reflections
------------------------------------------------------------------------
module Lambdaworld.Talk2 where


-- Import rebound library
import Rebound hiding (Ctx)
import Rebound.Bind.Pat qualified as Rebound.Pat (Bind)
import Rebound.Bind.Pat ( bind, getBody, getPat, instantiate )











------------------------------------------------------------------------
-- * Challenge: Lang where # of binding vars not statically known
------------------------------------------------------------------------
{-  

-- lambda calculus with unit, products, sums, and pattern matching

e ::= x | \ x . e | e1 e2 
   | () | (e1,e2) | Left e | Right e   
   | case e of { brs }                

-- list of branches
brs ::=   |  p -> e ; brs    

-- patterns
p ::= x | () | (p1,p2) | Left p | Right p | _ 

-}

------------------------------------------------------------------------
-- * Syntax and binding specification
------------------------------------------------------------------------

 
-- A pattern: m is the number of variables *bound* by the pattern
data Pat (m :: Nat) where
    PVar   :: Pat N1                              -- x
    PUnit  :: Pat N0                              -- ()
    PPair  :: Pat m1 -> Pat m2 -> Pat (m2 + m1)   -- (p1, p2)
    PLeft  :: Pat m -> Pat m                      -- Left p
    PRight :: Pat m -> Pat m                      -- Right p
    PWild  :: Pat N0                              -- wildcard _ 

-- rebound defines abstract type `Bind` that
-- binds `n` variables of type `Tm` in body of type `Tm` using pattern `p`
type Bind p n = Rebound.Pat.Bind Tm Tm p n

-- A list of pattern bindings of m variables, in scope n
-- Bind (Pat m) n contains a pattern (Pat m) and body (Tm (m + n))
data BranchList (n :: Nat) where
    BNil  :: BranchList n
    BCons :: Bind (Pat m) n -> BranchList n -> BranchList n






data Tm n = 
     TVar (Fin n)                    -- x 
   | TLam (Bind P1 n)                -- \x. e  -- binds 1 variable
   | TApp (Tm n) (Tm n)              -- e1 e2
   | TUnit                           -- ()
   | TPair (Tm n) (Tm n)             -- (e1, e2)
   | TLeft (Tm n)                    -- Left e
   | TRight (Tm n)                   -- Right e
   | TCase (Tm n) (BranchList n)     -- case e of { brs } 
     deriving (Generic1)

-- pattern that binds a single variable
data P1 = P1








-- \x . case x of { Left (Left x) -> Left x 
--                ; Left _        -> Right () 
--                ; Right y       -> Right () } 

p1 :: Pat N1
p1 = PLeft (PLeft PVar)

p2 :: Pat N0
p2 = PLeft PWild

p3 :: Pat N1
p3 = PRight PVar

example :: Tm n
example = TLam (bind P1 (TCase (TVar FZ) 
                             (BCons (bind p1 (TLeft (TVar FZ)))
                             (BCons (bind p2 (TRight TUnit))
                             (BCons (bind p3 (TRight TUnit))
                             BNil)))))
     





-----------------------------------------------------------------
-- API for abstract type Bind
-----------------------------------------------------------------


-- >>> :t bind







-- Any type that is used as a pattern *must* be an
-- instance of the `Sized` type class, so that the library
-- can determine the number of binding variables.

-- Any type that is used as the body of the binder 
-- *must* be an instance of the `Subst` type class, so that 
-- we can substitute into it.


-- Smart eliminator
-- >>> :t getPat



-- >>> :t getBody

-- >>> :t instantiate

-- Must instantiate *all* variables bound by the pattern, use `Env` 
-- record this instantiation.

instantiate1 :: (Sized p, Size p ~ N1) => Bind p n -> Tm n -> Tm n
instantiate1 b t = instantiate b (t .: zeroE) 



--------------------------------------------------------------------
-- Sized instances (counts bound variables)
--------------------------------------------------------------------

instance Sized (Pat m) where
    type Size (Pat m)  = m

    size :: Pat m -> SNat (Size (Pat m))
    size PVar          = s1
    size PUnit         = s0
    size PWild         = s0
    size (PPair p1 p2) = sPlus (size p2) (size p1)
    size (PLeft p)     = size p
    size (PRight p)    = size p


instance Sized P1 where
    type Size P1 = N1

    size :: P1 -> SNat (Size P1)
    size P1 = s1


------------------------------------------------------------
-- * ASIDE: SNat - singleton nats
------------------------------------------------------------
-- The type `SNat` provide *runtime* access to type-level 
-- natural numbers. This is because, in Haskell, numbers 
-- that appear in types are erased before execution.


-- s0 :: SNat N0

-- s1 :: SNat N1

-- sPlus :: SNat n1 -> SNat n2 -> SNat (n1 + n2)






--------------------------------------------------------------------
-- * Environments: `Env v m n` operations
--------------------------------------------------------------------



-- Some operations need to identify "var" constructor
-- because they need an identity substitution
instance SubstVar Tm where
  var :: Fin n -> Tm n
  var = TVar


-- TVar is an identity substitution 
-- >>> :t idE


-- "up" operation depends on TVar to leave index 0 alone
-- >>> :t up




--------------------------------------------------------------------
-- * Substitution
--------------------------------------------------------------------
-- applyE is a member of multiparameter type class "Subst v c"
--   v - type in codomain of environment
--   c - type that we are substituting into

instance Subst Tm Tm where 

  isVar (TVar x) = Just (Refl, x)
  isVar _ = Nothing

{-
  applyE :: Env Tm n m -> Tm n -> Tm m
  applyE r (TVar x)       = r ! x
  applyE r (TApp e1 e2)   = TApp (applyE r e1) (applyE r e2)
  applyE r (TLam b)       = TLam (applyE r b)
  applyE r TUnit          = TUnit
  applyE r (TPair e1 e2)  = TPair (applyE r e1) (applyE r e2)
  applyE r (TLeft e)      = TLeft (applyE r e)
  applyE r (TRight e)     = TRight (applyE r e)
  applyE r (TCase e brs)  = TCase (applyE r e) (applyE r brs)
-}

instance Subst Tm BranchList where

  applyE :: Env Tm n m -> BranchList n -> BranchList m
  applyE r (BCons b brs)  = BCons (applyE r b) (applyE r brs)
  applyE r BNil           = BNil










--------------------------------------------------------------------
-- * Generic Substitution (GHC.Generics)
--------------------------------------------------------------------

-- can use GHC.Generics by replacing applyE above with isVar

-- >>> :t isVar









--------------------------------------------------------------------
-- Evaluator with pattern matching
--------------------------------------------------------------------

-- | call-by-value evaluation function
-- no scope errors, but types can fail at runtime
eval :: Tm Z -> Maybe (Tm Z)
eval (TVar x)      = case x of {}
eval (TLam m)      = return (TLam m)
eval (TApp m n) = do
    mv <- eval m
    case mv of
      TLam b -> eval (instantiate1 b n) 
      _ -> Nothing
eval TUnit         = return TUnit
eval (TPair e1 e2) = do
    v1 <- eval e1
    v2 <- eval e2
    return (TPair v1 v2)
eval (TLeft m) = do
    t <- eval m
    return (TLeft t)
eval (TRight m) = do
    t <- eval m
    return (TRight t)
eval (TCase e brs) = do
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
patternMatch PVar v       = return (s1, oneE v)
patternMatch PWild v      = return (s0, zeroE)
patternMatch PUnit TUnit  = return (s0, zeroE)
patternMatch (PPair p1 p2) (TPair v1 v2) = do
    (m1, env1) <- patternMatch p1 v1   
    (m2, env2) <- patternMatch p2 v2  
    -- (.++) needs to know the length of env2, supply it implicitly using withSNat
    return (sPlus m2 m1, withSNat m2 $ env2 .++ env1)
patternMatch (PLeft p) (TLeft v)   = patternMatch p v
patternMatch (PRight p) (TRight v) = patternMatch p v
patternMatch _ _ = Nothing


-- >>> eval (TApp example (TRight TUnit))


-- >>> eval (TApp example (TLeft (TRight TUnit)))



--------------------------------------------------------------------
-- * Conclusion: What does Dependent Haskell buy?
--------------------------------------------------------------------

-- The type checker ensures that all operations preserve scopes 
--    - No scope errors in well-typed code!
--    - More expressive types provide more confidence  
--    - No proofs needed: every function in Part I was ordinary Haskell


-- Libraries save work and automate boilerplate
--    - Abstract types hide the clever parts (efficient implementations of Bind/Env)
--    - GHC.Generics derives substitution
--    - Rich interface guarantees correct usage


-- But there are costs...
--    - Error messages can be obscure
--    - Sometimes GHC needs help with type-level reasoning




-- When Dependent Haskell works, it is beautiful. 

--------------------------------------------------------------------
-- * Try it
--------------------------------------------------------------------
--   https://github.com/sweirich/rebound
--     library, tutorial, exercises, larger examples, and this talk








--- End of Part II








------------------------------------------------------------------------
-- * Bonus: Alpha-equivalence
------------------------------------------------------------------------
-- (==) is alpha-equivalence 

{-

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
  testEquality (PLeft p)  (PLeft p')  = testEquality p p'
  testEquality (PRight p) (PRight p') = testEquality p p'
  testEquality _ _ = Nothing

-}

------------------------------------------------------------------------
-- * Extra definitions 
------------------------------------------------------------------------

-- nicer name for applyEnv
(!) :: Env Tm n m -> Fin n -> Tm m
(!) = applyEnv

instance (Show P1) where show P1 = "P1"
deriving instance (Show (Tm n))
deriving instance (Show (Pat m))
deriving instance (Show (BranchList n))
instance (Sized p, Show p) => Show (Bind p n) where
  show b = "(bind " ++ show (getPat b) ++ " " ++ show (getBody b) ++ ")"
