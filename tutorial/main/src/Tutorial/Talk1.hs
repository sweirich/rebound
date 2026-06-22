{-


               Dependent Haskell FTW

                Stephanie Weirich
                sweirich@upenn.edu
            
              University of Pennsylvania
        (currently visiting University of Cambridge)

          https://sweirich.github.io/rebound/

    NOTE: website above includes lecture notes
          and link to github repository, including 
          library, examples, tutorial, exercises
          and this file.

-}



------------------------------------------------------------------------
--  Rebound library: Well-scoped de Bruijn indices in Haskell
------------------------------------------------------------------------

{-

    Noé De Santo, Stephanie Weirich, "Rebound: Efficient, 
    Expressive, and Well-Scoped Binding"
    Haskell Symposium 2025

    - Expressive: reimplemented pi-forall demo implementation of
      dependently-typed language
    - Efficient: implements of de Bruijn indices through delayed 
      and reified substitutions

    https://github.com/sweirich/rebound 



 -}

------------------------------------------------------------------------
-- Let's implement a small language 
------------------------------------------------------------------------

{-

t ::= Unit | t -> t | t * t | t + t

e ::= x | \ x . e | e1 e2 
   | unit            | case e0 of () -> e1
   | ( e1, e2 )      | case e0 of (x,y) -> e1
   | inj1 e | inj2 e | case e0 of { inj1 x -> e1 ; inj2 y -> e2 }

-}




------------------------------------------------------------------------
-- Big step, substitution based semantics:
------------------------------------------------------------------------
{-

------- val
v => v

e1 => \x.e 
e { e2 / x } => v         <- how do you implement substitution?
------------------ app
e1 e2 => v

e0 => (e2,e3)  e1{e2/x,e3/y} => v               <- multsubstitution?
--------------------------------- match-pair
case e0 of (x,y) -> e1 => v

e0 => inj1 e3     e1 { e3/x1 } => v
------------------------------------------------- match-left
case e0 of { inj1 x1 -> e1 ; inj2 x2 -> e2 } => v

-}

------------------------------------------------------------------------






{-     HOW???    -}







------------------------------------------------------------------------
-- Goals: 
------------------------------------------------------------------------
{-
   - Correctness: we want to be sure that we've implemented 
      *this* language, without any bugs

        ===> types give us confidence

   - Simplicity: we want a minimum of ceremony

        ===> good abstractions (and types) simplify our work

   - No limits: we want to do all the things that a practical 
    system might want

        ===> first-order representation (and good abstractions)

   - Efficiency: we want to be able to run the result

        ===> good abstractions (hiding slick tricks)

-}



------------------------------------------------------------------------
-- ANSWER:  rebound library
------------------------------------------------------------------------

{-

PART 1:  Talk1.hs: self-contained foundational introduction 

PART 2:  Talk2.hs: language definition with library support 
                   and pattern binding   

PART 3:  Talk3.hs: using well-scoped DB indices at scale  
                   e.g. parsing, scope checking, pretting 
                   printing, random testing, etc
         
-}






------------------------------------------------------------------------
-- | PART1:  What abstractions should the rebound library provide?
-- | Well-scoped de Bruijn term representations from scratch
module Tutorial.Talk1 where

------------------------------------------------------------------------
-- * Bounded natural numbers
------------------------------------------------------------------------

-- | Unary natural numbers, used as type-level scopes.
-- A term in scope @n@ has variables @0 .. n-1@.
data Nat where
  Z :: Nat 
  S :: Nat -> Nat

-- some (type-level) natural numbers
type N0 = Z
type N1 = S Z
type N2 = S (S Z)
type N3 = S (S (S Z))
type N4 = S N3

-- addition
type family (+) (n :: Nat) (m :: Nat) :: Nat where
   Z + m = m
   (S n) + m = S (n + m)




-- | @Fin n@ is the type of de Bruijn indices in scope n:
-- the finite set @{0, 1, ..., n-1}@.
-- `FZ` represents 0, and `FS x` represents @x + 1@.
data Fin n where
    FZ :: Fin (S n)
    FS :: Fin n -> Fin (S n)

-- NOTE: Fin is a *GADT* because the result type of each constructor mentions
-- "S n" instead of n.

-- Some example Fins
-- "0"
f0 :: Fin (S n)
f0 = FZ

-- "1" in any scope that has at least two numbers
f1 :: Fin (N2 + n)
f1 = FS f0

-- "2" in any scope that has at least three numbers
f2 :: Fin (N3 + n)
f2 = FS f1

-- "3" in any scope that has at least four numbers
f3 :: Fin (N4 + n)
f3 = FS f2



-- In Haskell we can derive equality  
-- functions automatically for datatypes
deriving instance (Eq (Fin n))

-- >>> f1 == f1




-- >>> f1 == f2





-- >>> (f1 :: Fin N2) == (f1 :: Fin N3)







-- | convert a fin into an integer
toInt :: Fin n -> Int
toInt FZ = 0
toInt (FS x) = 1 + toInt x


-- Custom function for displaying `Fin`
instance Show (Fin n) where
   show :: Fin n -> String
   show f = "f" ++ show (toInt f)


-- >>> f3











------------------------------------------------------------------------
-- * Well-scoped lambda calculus terms
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
    -- simple pattern matching
    -- `case e0 of () -> e1`
    MatchUnit :: Tm n -> Tm n -> Tm n
    -- `case e0 of (x,y) -> e1`
    MatchPair :: Tm n -> Bind2 n -> Tm n
    -- `case e0 of {inj1 x -> e1 ; inj2 y -> e2 }`
    MatchSum  :: Tm n -> Bind1 n -> Bind1 n -> Tm n
      deriving (Eq, Show)

-- | A term with one bound variable: a body in scope `S n` 
data Bind1 n where
    Bind1 :: Tm (S n) -> Bind1 n
      deriving (Eq, Show)

-- | A term with two bound variables: a body in scope `S (S n)`.
data Bind2 (n :: Nat) where
    Bind2 :: Tm (S (S n)) -> Bind2 n
      deriving (Eq, Show)


------------------------------------------------------------------------
-- * Examples
------------------------------------------------------------------------

-- | Identity function: λx. x  or  λ.0
ex_id :: Tm Z
ex_id = Lam (Bind1 (Var f0))

-- | Constant function: λx. λy. x or λ.λ.1
ex_const :: Tm Z
ex_const = Lam (Bind1 (Lam (Bind1 (Var f1))))

-- | Swap a pair: 
-- λp. case p of (x, y) → (y, x)  
-- λ. case 0 of (,) -> (0,1)
ex_swap :: Tm n
ex_swap = Lam (Bind1 (MatchPair (Var f0) (Bind2 (Pair (Var f0) (Var f1)))))


-- >>> ex_id == ex_id





------------------------------------------------------------------------
-- * Substitution environments
------------------------------------------------------------------------

-- | A substitution environment maps @m@ variables to terms in scope @n@.
-- It is like a vector of length m
type Env m n = Fin m -> Tm n

-- | If there are no variables in the domain, we can map to any scope
zeroE :: Env Z n
zeroE = \f -> case f of {}

-- | Extend an environment with a new term for the outermost variable.
-- `t .: env` maps `FZ` to t and `FS x` to `env x`.
-- Analogous to cons for a lists of terms.
infixr 5 .:
(.:) :: Tm n -> Env m n -> Env (S m) n
t .: env = \f -> case f of
    FZ   -> t      -- the new outermost variable maps to t
    FS x -> env x  -- all others delegate to env

-- EXAMPLES: 
-- all terms must be closed and there are three of them
-- exampleE :: Env N3 Z
exampleE = ex_id .: ex_const .: ex_swap .: zeroE

-- EXAMPLE: an identity substitution for terms with three free 
-- variables. We map each index to a variable with that index.
id3E :: Env N3 N3
id3E = Var f0 .: Var f1 .: Var f2 .: zeroE






-- | The identity environment: maps each variable to itself.
idE :: Env n n 
idE = Var   -- recall Var :: Fin n -> Tm n


-- | The shifting environment: increments the index of every variable by one
-- i.e. weakens a scope by introducing a fresh outermost variable.
shift :: Env m (S m)
shift x = Var (FS x)



------------------------------------------------------------------------
-- * Applying the substitution to terms
------------------------------------------------------------------------

-- | Apply a substitution environment to a term, replacing every free
-- variable @x@ with @env x@.  The environment is lifted under each
-- binder so that bound variables are not modified.
applyE :: Env m n -> Tm m -> Tm n
applyE env (Var x)              = env x
applyE env (Lam (Bind1 b))      = Lam (Bind1 (applyE (up env) b))
applyE _   Unit                 = Unit
applyE env (Pair a b)           = Pair (applyE env a) (applyE env b)
applyE env (Inj i t)            = Inj i (applyE env t)
applyE env (App f a)            = App (applyE env f) (applyE env a)
applyE env (MatchUnit a b)      = MatchUnit (applyE env a) (applyE env b)
applyE env (MatchPair a (Bind2 b)) =
    MatchPair (applyE env a) (Bind2 (applyE (up (up env)) b))
applyE env (MatchSum a (Bind1 b1) (Bind1 b2)) =
    MatchSum (applyE env a) (Bind1 (applyE (up env) b1)) (Bind1 (applyE (up env) b2))

-- | Lift an environment under one binder.
-- The new outermost variable `f0` maps to itself; all others are
-- shifted by one so that the result is in the extended scope.
up :: Env m n -> Env (S m) (S n)
up env = Var f0 .: applyE shift . env






-- | Compose two substitutions
(>>) :: Env m n -> Env n p -> Env m p
s1 >> s2 = applyE s2 . s1 






------------------------------------------------------------------------
-- * Binders and instantiation
------------------------------------------------------------------------

-- | Open a single-variable binder by substituting @t@ for the bound variable.
instantiate1 :: Bind1 n -> Tm n -> Tm n
instantiate1 (Bind1 body) t = applyE (t .: idE) body

-- | Open a two-variable binder by substituting @t1@ and @t2@ for the
-- two bound variables (outermost first).
instantiate2 :: Bind2 n -> Tm n -> Tm n -> Tm n
instantiate2 (Bind2 body) t1 t2 = applyE (t1 .: t2 .: idE) body

------------------------------------------------------------------------
-- * Evaluator
------------------------------------------------------------------------

-- | (big-step) cbv evaluation function 
eval :: Tm Z -> Maybe (Tm Z)
eval (Var x)      = case x of {}
eval (Lam m)      = return (Lam m)
eval Unit         = return Unit
eval (Pair e1 e2) = do 
    v1 <- eval e1 
    v2 <- eval e2 
    return (Pair v1 v2)
eval (Inj i m) = do
    t <- eval m
    return (Inj i t)
eval (App m n) = do
    mv <- eval m
    nv <- eval n
    case mv of 
        Lam b -> eval (instantiate1 b nv)
        _ -> Nothing
eval (MatchSum e0 m m') = do
    v <- eval e0
    case v of
        (Inj 0 v1) -> eval (instantiate1 m v1) 
        (Inj 1 v1) -> eval (instantiate1 m' v1)
        _ -> Nothing
eval (MatchPair e m) = do 
    v <- eval e 
    case v of
        Pair v1 v2 -> eval (instantiate2 m v2 v1)
        _ -> Nothing
eval (MatchUnit e m) = do
    v <- eval e
    case v of 
        Unit -> eval m
        _ -> Nothing




-- Question: How much of the code above can we package into a 
-- reusable library? How much is specific to the language we are implementing?

