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
    based on the "rebound" library for scope-safe binding

    Part I: 
      A DTP Pearl: Implementing the lambda calculus with 
         well-scoped de Bruijn indices

    Part II: 
      Using rebound at scale, and reflecting on Dependent Haskell

 -}







------------------------------------------------------------------------
--  Rebound library: Well-scoped de Bruijn indices in Haskell
------------------------------------------------------------------------
{-  
      https://github.com/sweirich/rebound 

    - Well-scoped: type system maintains domain-specific invariants
    - Expressive: didactic examples + pi-forall
    - Efficient: supports working with delayed and reified substitutions













    

    NOTE: the repository includes the rebound library, 
          examples, tutorial, exercises, pi-forall demo, and this talk.
    
    Noé De Santo, Stephanie Weirich, 
    "Rebound: Efficient, Expressive, and Well-Scoped Binding"
    Haskell Symposium 2025
 -}



------------------------------------------------------------------------
-- * Part I: A Dependently-Typed Pearl
------------------------------------------------------------------------

module Lambdaworld.Talk1 where
-- no imports in this part, we'll start from scratch











------------------------------------------------------------------------
-- * Bounded natural numbers in Haskell, as de Bruijn indices
------------------------------------------------------------------------
-- | Peano natural numbers (Zero and Successor)
data Nat = Z | S Nat

five :: Nat
five = S (S (S (S (S Z))))

-- | `Fin n` is the type of indices in "scope" n:
-- i.e. the finite set `{0, 1, ..., n-1}`.
data Fin n where
    FZ :: Fin (S n)
    FS :: Fin n -> Fin (S n)
    



f1' :: Fin (S (S Z))
f1' = FS FZ               

f1 :: Fin (S (S n))   -- The index 1 in any scope >= 2
f1 = FS FZ




-- f5 = FS (FS (FS (FS (FS FZ))))






------------------------------------------------------------------------
-- * Well-scoped lambda calculus terms, using de Bruijn indices
------------------------------------------------------------------------

-- AST for the lambda calculus
-- All alpha-equivalent terms have same representation
data Tm (n :: Nat) where
    Var   :: Fin n -> Tm n           -- variable     x       
    Lam   :: Tm (S n) -> Tm n        -- abstraction  λx. e
    App   :: Tm n -> Tm n -> Tm n    -- application  e1 e2


-- | Identity function: λx. x  or  λ.0
ex_id :: Tm Z
ex_id = Lam (Var FZ)


-- | Constant function: λx. λy. x or λ.λ.1
ex_const :: Tm Z
ex_const = Lam (Lam (Var (FS FZ)))


------------------------------------------------------------------------
-- * Scope-safe evaluator
------------------------------------------------------------------------
-- Only one kind of value in pure lambda calculus,
-- a closed lambda expression
newtype Val = VLam (Tm (S Z))

-- | Evaluation function (call-by-name) 
-- Haskell's type system ensures no *runtime* errors
eval :: Tm Z -> Val
eval (Var x)   = case x of {}     -- impossible case!
eval (Lam b)   = VLam b
eval (App m n) = eval (instantiate (eval m) n)


-- | Open a single-variable binder by substituting `t` for the bound variable.
instantiate :: Val -> Tm Z -> Tm Z
instantiate (VLam body) t = subst1 t body 



------------------------------------------------------------------------
-- * Internal vs. External verification
------------------------------------------------------------------------
{- 


Internal verification: use types to capture invariants 

        eval :: Tm Z -> Val








External verification: prove properties after the fact

        eval :: Tm -> Maybe Val

        pf  :: closed e -> exists v. eval e = Just v 
                           or diverges e




External verification is more common in Lean and Rocq.
Internal verification is more common in Agda and Haskell.





External verification is more general.
But, when internal verification works, it is concise (and beautiful).






We should treasure and display these pearls
     ... but not be surprised by their rarity.

-}



------------------------------------------------------------------------
-- * How do we implement instantiate? 
------------------------------------------------------------------------


-- instantiate :: Val -> Tm Z -> Tm Z
-- instantiate (VLam b) a = subst1 a b
--    ... i.e. substitute a for *single* free variable in b







-- ANSWER: We need scope-safe substitution

subst1 :: Tm Z -> Tm (S Z) -> Tm Z
subst1 a b = applyE (a .: Var) b




-- ... generalized to all free variables in the term

substN :: Vec n (Tm Z) -> Tm n -> Tm Z
substN e b = applyE e b 




-- ... and generalized to open terms in the substitution

subst :: Vec n (Tm m) -> Tm n -> Tm m
subst = applyE






-- ACK: Bird & Patterson, Conor Titania McBride, and many others






------------------------------------------------------------------------
-- * Vectors - Maps from indices to data
------------------------------------------------------------------------
type Vec n a = Fin n -> a    -- only one of many ways to implement Vec


-- | empty vector contains no data
vnil :: Vec Z a 
vnil = \x -> case x of {}


-- | "cons" increase the scope by one
infixr 5 .:
(.:) :: a -> Vec n a -> Vec (S n) a
x .: xs = \f -> case f of { FZ -> x ; FS f -> xs f }


-- | "lookup" the value at a specific index
(!) :: Vec n a -> Fin n -> a
v ! x = v x


example = "L" .: "A" .: "M" .: "B" .: "D" .: "A" .: vnil






-- >>> example ! f1






-- >>>  ("L" .: vnil) ! f1





------------------------------------------------------------------------
-- * Environments: multisubstitutions & their operations 
------------------------------------------------------------------------
-- | A substitution maps `m` variables to terms in scope `n`.
type Env m n = Vec m (Tm n)

-- | Apply a substitution to a term, replacing *every* free variable  
applyE :: Env m n -> Tm m -> Tm n
applyE env (Var x)        = env ! x
applyE env (App f a)      = App (applyE env f) (applyE env a)
applyE env (Lam b)        = Lam (applyE (up env) b)













-- | Lift under one binder: New variable maps to itself; 
-- all others are shifted to the extended scope.
up :: Env m n -> Env (S m) (S n)
up env = Var FZ .: shiftE env

-- | Shift an environment to a new scope
shiftE :: Env n m -> Env n (S m)
shiftE env = env .>> (idE . FS)

-- | Identity enviroment -- doesn't change the scope
idE :: Env n n
idE = Var

-- Compose environments (apply the second to the range of the first)
(.>>) :: Env m n -> Env n p -> Env m p
e1 .>> e2 = applyE e2 . e1





-- EXAMPLE
-- | [ x0 ↦ x0, x1 ↦ (x0 x0) ] 
-- 
env0 :: Vec (S (S Z)) (Tm (S n))
env0 = Var FZ .: App (Var FZ) (Var FZ) .: vnil

-- >>> applyE env0 (Var FZ) 









------------------------------------------------------------------------
-- * Transition: building a library for variable binding
------------------------------------------------------------------------

-- * Environment data structure `Env m n`

{-
-- lookup a variable (total operation!)
(!)  :: Env m n -> Fin m -> Tm n

-- extend with new definition (cons)
(.:) :: Tm n -> Env m n -> Env (S m) n

-- lift under binder: new variable maps to itself; 
-- all others are shifted to the extended scope
up   :: Env m n -> Env (S m) (S n)

-- shift to a larger scope
shiftE :: Env n m -> Env n (S m)

-- identity, does not modify scope
idE  :: Env n n

-- compose two binders
(.>>) :: Env m n -> Env n p -> Env m p

-}


------------------------------------------------------------------------
-- * Efficient ?
------------------------------------------------------------------------

-- "applyE" weakens each term in the range of env
-- But, going under *every* binder shifts---this composition is expensive!











------------------------------------------------------------------------
-- * Delaying and fusing traversals
------------------------------------------------------------------------

-- (1) Delay substitution at binders

data Bind n where
  Bind :: Env m n -> Tm (S m) -> Bind n 
       -- ^^^^^^^ store a delayed substitution at binder

instantiate1 :: Bind n -> Tm n -> Tm n
instantiate1 (Bind e body) v = applyE (v .: e) body

-- (2) Delay shifting in environments, smart composition combines
-- multiple shifts into one pass


-- ACK: implementation of Agda / Rocq type checkers
-- See https://mathisbd.github.io/blog/esubstitutions.html










-- End of Part I ---





------------------------------------------------------------------------
-- * Extra definitions
------------------------------------------------------------------------

deriving instance Show (Tm n)

deriving instance Eq Nat

instance Eq (Fin n) where
  FZ == FZ = True
  (FS f1) == (FS f2) = f1 == f2
  _ == _ = False

instance Show Nat where
  show n = show (fromNat n)

instance Show (Fin n) where
  show f = "f" ++ show (toNat f)

instance Num Nat where
  fromInteger 0 = Z
  fromInteger n | n > 0 = S (fromInteger (n-1))
  fromInteger n = error "cannot convert negative number to Nat"
  Z + m = m
  S n + m = S (n + m)
  Z * _ = Z
  S n * m = m + n * m
  n - Z = n
  S n - S m = n - m
  Z - S _ = error "cannot subtract to a negative Nat"
  abs n = n
  signum Z = Z
  signum (S _) = S Z


fromNat :: Nat -> Int
fromNat Z = 0
fromNat (S n) = 1 + fromNat n 

toNat :: Fin n -> Nat
toNat FZ = Z
toNat (FS n) = S (toNat n)


