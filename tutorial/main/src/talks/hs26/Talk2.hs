{- 

  Part II: Another "Pearl" -- dependently-typed environments
    via ShiftLists

-}

module Talks.Hs26.Talk2 where

-- Use library definitions for Nat, Fin, etc.
import Data.Fin
import Rebound.Lib hiding (Vec)

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
-- * Need environments with rich interface
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
up s = Var FZ .: shiftE s 

-- shift to a larger scope
shiftE :: Env n m -> Env n (S m)

------------------------------------------------------------------------
-- * Many implementations
------------------------------------------------------------------------

-- Functions (e.g. Fin m -> Tm n, from Part I)
-- Length-indexed lists (e.g. Vec m (T n))
-- Defunctionalized interface (cf. Agda)
-- Shift-Skewed binary tree (cf. Rocq)

-- OR: non-dependent implementation using phantom types

-- NOTE: Claude is very good at ornamentation








------------------------------------------------------------
-- * ShiftLists
------------------------------------------------------------

-- Recall:
--    up env = Var FZ .: shift env
--
--    shiftE env = applyE (Var . FS) . env
-- 
-- "applyE" weakens each term in the range of env
-- But, *every* binder shifts---this is expensive!
-- Can we fuse multiple traversals?




-- **Key idea**: represent env as a length-indexed list, with 
-- interspersed, **delayed** n-ary shifting

-- (This is a *very* simplified version of Rocq's implementation.
-- adapted from https://mathisbd.github.io/blog/esubstitutions.html
-- and ornamented with scope indices.)

------------------------------------------------------------
-- * ShiftList implementation
------------------------------------------------------------

data Env m n where 
  Id    :: Env m m  
  Cons  :: Tm n -> Env m n -> Env (S m) n
  Shift :: SNat k -> Env m n -> Env m (k + n)

idE  = Id

(.:) = Cons

-- smart "shift" operation, fuses multiple shifts
shiftE (Shift k e) = Shift (sPlus s1 k) e
shiftE e           = Shift s1 e





------------------------------------------------------------
-- * ASIDE: SNat - singleton nats
------------------------------------------------------------

-- The type `SNat` provide *runtime* access to type-level 
-- natural numbers. This is because, in Haskell, numbers 
-- that appear in types are erased before execution.

-- >>> :t s0

-- >>> :t s1

-- >>> :t sPlus

-- >>> toInt (sPlus s2 s3)



------------------------------------------------------------
-- * SNat - in action
------------------------------------------------------------

-- Can use SNat to shift `Fin` indices to new scopes.

-- >>> :t shiftN

-- >>> shiftN s2 (f1 :: Fin N3)







------------------------------------------------------------
-- * Implementation of (!) with embedded shifts
------------------------------------------------------------

-- Recall type of environment
-- >>> :i Env


-- | As we traverse the list, accumulate amount to shift and 
-- apply it all at once, fusing multiple traversals
env ! x = lookupRec s0 env x

lookupRec :: forall k m n.
    SNat k -> Env m n -> Fin m -> Tm (k + n)
lookupRec k s i = 
    case s of 

        Id  -> Var (shiftN k i)
--                  ^^^^^^ shift index by k

        Cons t ss -> case i of 
            FZ   -> applyE (Shift k Id) t  
--                  ^^^^^^^^^^^^^^^^^^^  increment all vars in t by k                   
            FS j -> lookupRec k ss j

        Shift (j :: SNat j) (ss :: Env m p) 
--                                       ^^  n ~ (j + p)
            | Refl <- axiomAssoc @k @j @p ->
--            ^^^^    k + (j + p) ~ (k + j) + p            
            lookupRec (sPlus k j) ss i :: Tm ((k + j) + p)
                  







------------------------------------------------------------------
-- * Associativity axiom
------------------------------------------------------------------

-- Associativity axiom returns a witness for type equality

-- >>> :i Refl

-- >>> :t axiomAssoc

-- | "Proof" of associativity
lemmaAssoc :: forall m n p. SNat p -> p + (m + n) :~: (p + m) + n
lemmaAssoc p = case snat_ p of 
            SZ_ -> Refl
            SS_ p1 | Refl <- lemmaAssoc @m @n p1
                   -> Refl







{- NB: compare to Agda version of proof:

-- | Agda Proof 
@0 assoc : ∀ (@0 p : Nat) {@0 m n} → p + (m + n) ≡ (p + m) + n
assoc Z     = Refl
assoc (S p) = cong S (assoc p)
--            ^^^^  must explicitly use congruence

-- Congruence: equals give equals under any function.
@0 cong : ∀ {A B : Set} (f : A → B) {@0 x y : A} → x ≡ y → f x ≡ f y
cong f Refl = Refl

-}





------------------------------------------------------------------
-- * Associativity lemma
------------------------------------------------------------------

-- So why does axiomAssoc use unsafeCoerce?

-- We don't want to use lemmaAssoc !
--   + Haskell has to *run* the proof to make sure that it is real
--   + SNat p is not available where we need the lemma, so we  
--     have to pass it around.







------------------------------------------------------------------
-- * How many axioms do we need?
------------------------------------------------------------------

-- 
-- Nat-indexed scopes are degenerate lists (i.e. typing contexts) 
-- Only need monoid properties:
--       Z + n ~ n                   -- true by definition
--       n + Z ~ n                   -- axiomPlusZ
--       p + (m + n) ~ (p + m) + n   -- axiomAssoc







------------------------------------------------------------------
-- * Could Haskell do better?
------------------------------------------------------------------


-- Coercion evidence (i.e. equality proof) is eraseable, so must be 
-- expressed in a consistent language.
--
-- For more expressiveness: extend GHC's coercion language to include 
-- induction. Blueprint in:
-- 
--    Yiyun Liu and Stephanie Weirich. "Dependently-Typed Programming 
--    with Logical Equality Reflection", ICFP 2023.
   

