{-


          Adventures in Dependent Haskell: 
              Well-scoped expressions

                Stephanie Weirich
                sweirich@upenn.edu
            
              University of Pennsylvania

                 Lambda World
                 October 2026

-}


------------------------------------------------------------------------
--  Talk Plan
------------------------------------------------------------------------

{-

    Examples of dependently-typed programming (DTP) in Haskell, 
    inspired by rebound library

    Part I: A DTP Pearl: Well-scoped de Bruijn indices
    Part II: Using rebound at scale, and reflecting on Dependent Haskell

 -}


------------------------------------------------------------------------
--  Rebound library: Well-scoped de Bruijn indices in Haskell
------------------------------------------------------------------------
{-  Noé De Santo, Stephanie Weirich, "Rebound: Efficient, 
    Expressive, and Well-Scoped Binding"
    Haskell Symposium 2025

    - Efficient: supports working with delayed and reified substitutions
    - Expressive: reimplemented pi-forall 
    - Well-Scoped: type system maintains domain-specific invariant

    https://github.com/sweirich/rebound 

    NOTE: the github repository includes the rebound library, 
          examples, tutorial, exercises, pi-forall demo, and this talk.
 -}



------------------------------------------------------------------------
-- * Part I: A Dependently-Typed Pearl
------------------------------------------------------------------------

module Talks.Lambdaworld.Talk1 where
-- no imports in this part, we'll start from scratch








------------------------------------------------------------------------
-- * Internal verification example in Haskell
------------------------------------------------------------------------
-- | Peano natural numbers
data Nat = Z | S Nat

-- | `Fin n` is the type of de Bruijn indices in scope n:
-- the finite set `{0, 1, ..., n-1}`.
data Fin n where
    FZ :: Fin (S n)
    FS :: Fin n -> Fin (S n)
    
f1 :: Fin (S (S n))   -- Any scope >= 2
f1 = FS FZ

------------------------------------------------------------------------
-- * Vectors - Fin delimits the domain of the function
------------------------------------------------------------------------
type Vec n a = Fin n -> a

vnil :: Vec Z a 
vnil = \x -> case x of {}

infixr 5 .:
(.:) :: a -> Vec n a -> Vec (S n) a
x .: xs = \f -> case f of { FZ -> x ; FS f -> xs f }

(!) :: Vec n a -> Fin n -> a
v ! x = v x

-- Out-of-domain access is compile-time failure
-- >>>  ("a" .: vnil) ! f1
-- Couldn't match type 'S n0_aLdTl[tau:1] with 'Z
-- Expected: Fin ('S 'Z)
--   Actual: Fin ('S ('S n0_aLdTl[tau:1]))
-- In the second argument of `(!)', namely `f1'
-- In the expression: ("a" .: vnil) ! f1
-- In an equation for `it_aLdRU': it_aLdRU = ("a" .: vnil) ! f1


------------------------------------------------------------------------
-- * Internal vs. External verification
------------------------------------------------------------------------

{- 

Internal verification is more common in Agda.
External verification is more common in Lean/Rocq.

External verification is more general.
But, when internal verification works, it is beautiful.

We should treasure and display these pearls
     ... but not be surprised by their rarity.

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
type Env m n = Vec m (Tm n)

-- | Apply an environment to a term, replacing every free variable  
applyE :: Env m n -> Tm m -> Tm n
applyE env (Var x)        = env ! x
applyE env (Lam b)        = Lam (applyE (up env) b)
applyE env (App f a)      = App (applyE env f) (applyE env a)

-- | Lift under one binder: New variable maps to itself; 
-- all others are shifted to the extended scope.
up :: Env m n -> Env (S m) (S n)
up env = Var FZ .: shiftE env

-- Compose environments (apply the second to the range of the first)
(.>>) :: Env m n -> Env n p -> Env m p
e1 .>> e2 = applyE e2 . e1

-- | Shift an environment to a new scope
shiftE :: Env n m -> Env n (S m)
shiftE env = env .>> (Var . FS)






------------------------------------------------------------------------
-- * Evaluator: Internal verification for well-scoped terms
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
instantiate (VLam body) t = applyE (t .: Var) body

-- | Identity enviroment -- doesn't change the scope
idE :: Env Z Z
idE = Var

nilE :: Env Z n
nilE = \x -> case x of {}


------------------------------------------------------------------------
-- * Transition: building a library for variable binding
------------------------------------------------------------------------

-- * Environment data structure `Env m n`

{-
-- lookup a variable (total operation!)
(!)  :: Env m n -> Fin m -> Tm n

-- identity, does not modify scope
idE  :: Env n n

-- extend with new definition (cons)
(.:) :: Tm n -> Env m n -> Env (S m) n

-- lift under binder: new variable maps to itself; 
-- all others are shifted to the extended scope
up   :: Env m n -> Env (S m) (S n)

-- compose two binders
(.>>) :: Env m n -> Env n p -> Env m p

-- shift to a larger scope
shiftE :: Env n m -> Env n (S m)
-}


------------------------------------------------------------------------
-- * Efficient implementations for environments 
------------------------------------------------------------------------

-- Recall:
--    up env = Var FZ .: shiftE env
--
--    shiftE env = env .>> (Var . FS) 
-- 
-- "applyE" weakens each term in the range of env
-- But, going under *every* binder shifts---this composition is expensive!

------------------------------------------------------------------------
-- * Fusing multiple traversals
------------------------------------------------------------------------

-- (1) Delay substitution at binders

data Bind n where
  Bind :: Env m n -> Tm (S m) -> Bind n 

instantiate1 :: Bind n -> Tm n -> Tm n
instantiate1 (Bind e body) v = applyE (v .: e) body

-- (2) Delay shifting in the data structure

-- data Env m n where
--   Id    :: Env m m
--   Cons  :: Tm n -> Env m n -> Env (S m) n
--   Shift :: SNat k -> Env m n -> Env m (k + n)   -- multiple shifts at once




------------------------------------------------------------
-- * SNat - singleton nats
------------------------------------------------------------
-- The type `SNat` provide *runtime* access to type-level 
-- natural numbers. This is because, in Haskell, numbers 
-- that appear in types are erased before execution.


-- s0 :: SNat N0

-- s1 :: SNat N1

-- sPlus :: SNat n1 -> SNat n2 -> SNat (n1 + n2)









-- End of Part I ---





------------------------------------------------------------------------
-- * Extra definitions
------------------------------------------------------------------------

deriving instance Eq Nat

instance Eq (Fin n) where
  FZ == FZ = True
  (FS f1) == (FS f2) = f1 == f2
  _ == _ = False

instance Show Nat where
  show n = show (fromNat n)

instance Show (Fin n) where
  show f = show (toNat f)

instance Num Nat where
  fromInteger 0 = Z
  fromInteger n | n > 0 = S (fromInteger (n-1))
  fromInteger n = error "cannot convert negative number to Nat"
  (*) = undefined
  (+) = undefined
  abs = undefined
  signum = undefined
  (-) = undefined


fromNat :: Nat -> Int
fromNat Z = 0
fromNat (S n) = 1 + fromNat n 

toNat :: Fin n -> Nat
toNat FZ = Z
toNat (FS n) = S (toNat n)


