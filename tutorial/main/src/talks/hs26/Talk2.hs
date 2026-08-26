{- 

  Part II: Another "Pearl" -- dependently-typed environments
    via Shift Lists

-}

module Talks.Hs26.Talk2 where

import Data.Fin
import Rebound.Lib

------------------------------------------------------------
-- * Recap of Part I: Well-scoped AST + interpreter
------------------------------------------------------------
data Tm n = Var (Fin n) | App (Tm n) (Tm n) | Lam (Tm (S n))
  deriving (Eq, Show)

newtype Val = VLam (Tm (S Z))

eval :: Tm Z -> Val
eval (Var x)   = case x of {}     -- impossible case
eval (Lam b)   = VLam b
eval (App m n) = eval (instantiate (eval m) n)
   where instantiate (VLam b) t = applyE (t .: idE) b

applyE :: Env m n -> Tm m -> Tm n
applyE env (Var x)     = env ! x
applyE env (App t1 t2) = App (applyE env t1) (applyE env t2)
applyE env (Lam t)     = Lam (applyE (up env) t)

------------------------------------------------------------
-- * Need first-class environments with rich interface
------------------------------------------------------------

-- lookup a variable (total operation!)
(!)  :: Env m n -> Fin m -> Tm n
-- identity substitution, does not modify scope 
idE  :: Env n n
-- extend with new definition (cons)
(.:) :: Tm n -> Env m n -> Env (S m) n
-- lift under binder: new variable maps to itself; 
-- all others are shifted to the extended scope
up   :: Env m n -> Env (S m) (S n)


------------------------------------------------------------------------
-- * Many implementations
------------------------------------------------------------------------

{-

- Functions (e.g. Fin m -> Tm n, from Part I)
- Length-indexed lists (e.g. Vec m (T n))
- Defunctionalized interface (cf. Agda)
- Shift-Skewed binary tree (cf. Rocq)

- OR: non-dependent implementation using phantom types

NOTE: Claude is very good at ornamentation

-}


------------------------------------------------------------
-- * ShiftLists
------------------------------------------------------------

-- Recall:
--    up env = Var FZ .: (applyE shift . env)
-- 
-- "applyE shift" weakens each term in the range of env
-- But, we don't want to be too eager!
--    + may not access this term (if var unused)
--    + every binder shifts, want to fuse multiple traversals
--      into a single pass

-- **Key idea**: represent as a length-indexed list, with 
-- interspersed delayed n-ary shifting

-- (This is a *very* simplified version of Rocq's implementation.
-- adapted from https://mathisbd.github.io/blog/esubstitutions.html
-- and ornamented with scope indices)

------------------------------------------------------------
-- * ShiftList implementation
------------------------------------------------------------

data Env m n where 
  Id    :: Env m m  
  Cons  :: Tm n -> Env m n -> Env (S m) n
  Shift :: SNat k -> Env m n -> Env m (k + n)

idE  = Id

(.:) = Cons

up s = Var FZ .: Shift s1 s 
--               ^^^^^^^^^^  equivalent to "applyE shift . env"

-- increment all free variables in the term by 'k'
weaken :: SNat k -> Tm n -> Tm (k + n)
weaken k = applyE (Shift k Id) 

------------------------------------------------------------
-- * ASIDE: SNat - singleton nats
------------------------------------------------------------

-- The type `SNat` provide *runtime* access to 
-- type-level natural numbers. Haskell is not a full-spectrum 
-- dependently-typed language, so numbers that appear in types 
-- are erased before execution (like types).

-- >>> :t s0

-- >>> :t s1


-- >>> :t sPlus


-- >>> toInt (sPlus s2 s3)
-- 5

------------------------------------------------------------
-- * Implementation of look up operation for Vec
------------------------------------------------------------

data List m n where
  VId   :: List n n
  VCons :: Tm n -> List m n -> List (S m) n

vlookup :: List m n -> Fin m -> Tm n
vlookup s i = 
  case s of 
    VId -> Var i
    VCons t ss -> case i of 
                    FZ -> t
                    FS j -> vlookup ss j


------------------------------------------------------------
-- * Implementation of with embedded shifts
------------------------------------------------------------

{-
data Env m n where 
  Id    :: Env m m  
  Cons  :: Tm n -> Env m n -> Env (S m) n
  Shift :: SNat k -> Env m n -> Env m (k + n)
-}


-- | As we traverse the list, accumulate the shifting amount and 
-- apply it all at once
env ! x = lookupRec s0 env x

lookupRec :: forall k m n.
    SNat k -> Env m n -> Fin m -> Tm (k + n)
lookupRec k s i = 
    case s of 

        Id  -> Var (shiftN k i)
--                  ^^^^^^ increment index by k

        Cons t ss -> case i of 
            FZ   -> weaken k t  
--                  ^^^^^^  increment all vars in t by k                   
            FS j -> lookupRec k ss j

        Shift (j :: SNat j) (ss :: Env m p) 
--                                       ^^  n ~ (j + p)
            | Refl <- axiomAssoc @k @j @p ->
            
            lookupRec (sPlus k j) ss i :: Tm ((k + j) + p)
--                     ^^^^^^^^^^ recursive call adding j to accumulator                     


------------------------------------------------------------------
-- * Associativity axiom
------------------------------------------------------------------

-- >>> :t axiomAssoc
-- axiomAssoc :: p + (m + n) :~: (p + m) + n

{-
   With propositional equality, associativity of addition
   is provable:

    data (:~:) a b where 
      Refl :: a :~: a

-}

lemmaAssoc :: forall m n p. SNat p -> p + (m + n) :~: (p + m) + n
lemmaAssoc p = case snat_ p of 
            SZ_ -> Refl
            SS_ p1 -> case lemmaAssoc @m @n p1 of
                        Refl -> Refl

-- We don't want to use lemmaAssoc !
--    Haskell has to run the proof to make sure that it is not bottom
--    SNat p is not available where we need the lemma, would need to fish it around

-- axiomAssoc uses unsafeCoerce to provide this equality at no cost


-- Nat-indexed scopes are degenerate lists (i.e. typing contexts) 
-- Only need monoid properties:
--       Z + n ~ n                   -- true by definition
--       n + Z ~ n                   -- axiomPlusZ
--       p + (m + n) ~ (p + m) + n   -- axiomAssoc

------------------------------------------------------------------
-- * What could we do instead?
------------------------------------------------------------------

{- 

Haskell's explicit division between eraseable / noneraseable 
arguments should be maintained

Coercion evidence (i.e. equality proof) are eraseable, so must be 
expressed in consistent language

For more expressiveness: extend coercion language to include 
induction. Blueprint in:

Yiyun Liu and Stephanie Weirich. "Dependently-Typed Programming 
   with Logical Equality Reflection", ICFP 2023.
   
-}

