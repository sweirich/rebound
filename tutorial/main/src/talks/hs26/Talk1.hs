{-


             What have we learned about 
            Dependently Typed Programming 
                 from Haskell?

                Stephanie Weirich
                sweirich@upenn.edu
            
              University of Pennsylvania

                 Haskell Symposium
                   August 2026

-}


------------------------------------------------------------------------
--  Talk Plan
------------------------------------------------------------------------

{-

    Examples of dependently-typed programming (DTP) in Haskell, inspired 
    by rebound library

    Part I: A DTP Pearl: Well-scoped de Bruijn indices
    Part II: A DTP "Pearl": Substitutions via shift lists
    Part III: Reflecting on DTP in Haskell

 -}


------------------------------------------------------------------------
--  Rebound library: Well-scoped de Bruijn indices in Haskell
------------------------------------------------------------------------

{-

    Noé De Santo, Stephanie Weirich, "Rebound: Efficient, 
    Expressive, and Well-Scoped Binding"
    Haskell Symposium 2025

    - Efficient: supports working with delayed and reified substitutions
    - Expressive: reimplemented pi-forall demo implementation of
      dependently-typed language
    - Well-Scoped: Haskell's type system maintains domain-specific invariant

    https://github.com/sweirich/rebound 

    NOTE: the github repository includes the rebound library, 
          examples, tutorial, exercises, pi-forall demo,
          and this talk.

 -}



------------------------------------------------------------------------
-- * Part I: A Dependently-Typed Pearl
------------------------------------------------------------------------

module Talks.Hs26.Talk1 where
-- no imports in this part, we'll start from scratch

------------------------------------------------------------------------
-- * External verification
------------------------------------------------------------------------

-- | Unary natural (Peano) numbers
data Nat where
  Z :: Nat 
  S :: Nat -> Nat

n1 :: Nat
n1 = S Z

-- A sequence is built like a list, but indexable via natural numbers
type Seq a = Nat -> Maybe a

snil :: Seq a 
snil = \x -> Nothing

scons :: a -> Seq a -> Seq a 
scons x xs = \f -> case f of 
                    Z -> Just x
                    S n -> xs n

example :: Seq String
example = scons "a" snil

-- Out-of-domain access is runtime failure
-- >>> example n1
-- Nothing

-- External verification is not generally available within Haskell
-- but supported through various tools (LiquidHaskell, hs2coq, etc)

------------------------------------------------------------------------
-- * Internal verification - GADT based
------------------------------------------------------------------------

-- | `Fin n` is the type of de Bruijn indices in scope n:
-- the finite set `{0, 1, ..., n-1}`.
data Fin n where
    FZ :: Fin (S n)
    FS :: Fin n -> Fin (S n)
    
f1 :: Fin (S (S Z))
f1 = FS FZ

-- Fin delimits the domain of the function    
type Vec n a = Fin n -> a

vnil :: Vec Z a 
vnil = \x -> case x of {}

infixr 5 .:
(.:) :: a -> Vec n a -> Vec (S n) a
x .: xs = \f -> case f of 
                  FZ -> x
                  FS f -> xs f


-- Out-of-domain access is compile-time failure
-- >>>  ("a" .: vnil) ! f1

------------------------------------------------------------------------
-- * Internal vs. External verification
------------------------------------------------------------------------

{- 

Internal verification is more common in Agda
External verification is more common in Lean/Rocq

External verification is more general
  - vectors can only reason about domains/indexing

But, when internal verification works, it is beautiful.

  - we should treasure and display these pearls
  - ... but not be surprised by their rarity

-}


------------------------------------------------------------------------
-- * Well-scoped lambda calculus terms
------------------------------------------------------------------------

data Tm (n :: Nat) where
    Var   :: Fin n -> Tm n
    Lam   :: Tm (S n) -> Tm n
    App   :: Tm n -> Tm n -> Tm n


-- | Identity function: λx. x  or  λ.0
ex_id :: Tm Z
ex_id = Lam (Var FZ)

-- | Constant function: λx. λy. x or λ.λ.1
ex_const :: Tm Z
ex_const = Lam (Lam (Var (FS FZ)))


------------------------------------------------------------------------
-- * Substitution
------------------------------------------------------------------------

-- | A substitution environment maps `m` variables to terms in scope `n`.
type Env m n = Fin m -> Tm n

-- | Apply a substitution environment to a term, replacing every free
-- variable  
applyE :: Env m n -> Tm m -> Tm n
applyE env (Var x)        = env x
applyE env (Lam b)        = Lam (applyE (up env) b)
applyE env (App f a)      = App (applyE env f) (applyE env a)

-- | Lift under one binder
-- New variable maps to itself; all others are shifted 
-- to the extended scope.
up :: Env m n -> Env (S m) (S n)
up env = Var FZ .: applyE shift . env

shift :: Env n (S n)
shift = Var . FS

------------------------------------------------------------------------
-- * Evaluator
------------------------------------------------------------------------

-- Only one kind of value in pure lambda calculus
newtype Val = VLam (Tm (S Z))

-- | (big-step) cbn evaluation function 
-- Haskell's type system ensures no *runtime* errors
eval :: Tm Z -> Val
eval (Var x)   = case x of {}     -- impossible case
eval (Lam b)   = VLam b
eval (App m n) = eval (instantiate (eval m) n)

    

-- | Open a single-variable binder by substituting `t` for the bound variable.
instantiate :: Val -> Tm Z -> Tm Z
instantiate (VLam body) t = applyE (t .: vnil) body

------------------------------------------------------------------------
-- * Internal verification for well-scoped terms
------------------------------------------------------------------------

-- Small step 
step :: Tm Z -> Maybe (Tm Z)
step (App (Lam b) n) = Just (instantiate (VLam b) n)
step (App m n) | Just m' <- step m 
               = Just (App m' n)
step _ = Nothing

{- 

- Internal verification provides an automatic precondition to eval

- Not every property about eval be stated using internal verification

      step :: Tm Z -> Tm Z

      lemma step_sound :: forall t1 t2,
         step t1 = Just t2 -> 
         eval t1 = eval t2 

      In Haskell, with QuickCheck, this property can be *tested* not 
      proven. (Tutorial material on generating well-scoped/well-typed 
      expressions are availble.)

-}

