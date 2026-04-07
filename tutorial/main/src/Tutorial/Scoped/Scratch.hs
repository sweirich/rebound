-- | Well-scoped de Bruijn term representations from scratch.
module Tutorial.Scoped.Scratch where

------------------------------------------------------------------------
-- * Finite sets
------------------------------------------------------------------------

-- | Unary natural numbers, used as type-level scopes.
-- A term in scope @n@ has variables @0 .. n-1@.
data Nat = Z | S Nat

-- some (type-level) natural numbers
type N1 = S Z
type N2 = S (S Z)
type N3 = S (S (S Z))

-- | @Fin n@ is the type of de Bruijn indices in scope @n@:
-- the finite set @{0, 1, ..., n-1}@.
-- @FZ@ represents @0@, and @FS x@ represents @x + 1@.
data Fin n where
    FZ :: Fin (S n)
    FS :: Fin n -> Fin (S n)

-- In Haskell we can derive equality and string conversion 
-- functions automatically for datatypes
deriving instance (Eq (Fin n))
deriving instance (Show (Fin n))


-- "1" in any scope that has at least two numbers
f1 :: Fin (S (S n))
f1 = FS FZ

-- "2" in any scope that has at least three numbers
f2 :: Fin (S (S (S n)))
f2 = FS (FS FZ)

-- "3" in any scope that has at least four numbers
f3 :: Fin (S (S (S (S n))))
f3 = FS (FS (FS FZ))


-- >>> :t (f1 :: Fin N3)


-- >>> :t (f2 :: Fin N3)



------------------------------------------------------------------------
-- * Types, terms and binders
------------------------------------------------------------------------

data Ty = One | Ty :-> Ty | Ty :* Ty | Ty :+ Ty
  deriving (Eq, Show)

data Tm (n :: Nat) where
    Var   :: Fin n -> Tm n
    Lam   :: Bind1 n -> Tm n
    Unit  :: Tm n
    Pair  :: Tm n -> Tm n -> Tm n
    Inj   :: Int -> Tm n -> Tm n
    -- application `e0 e1`
    App   :: Tm n -> Tm n -> Tm n
    -- simple pattern matching
    -- `case e0 of () -> e1`
    MatchUnit :: Tm n -> Tm n -> Tm n
    -- `case e0 of (x,y) -> e1`
    MatchPair :: Tm n -> Bind2 n -> Tm n
    -- `case e0 of {inj1 x -> e1 ; inj2 y -> e2 }`
    MatchSum  :: Tm n -> Bind1 n -> Bind1 n -> Tm n
      deriving (Eq, Show)

-- | A term with one bound variable: a body in scope @S n@ packaged
-- so that the binder is not visible outside.
data Bind1 n where
    Bind1 :: Tm (S n) -> Bind1 n
      deriving (Eq, Show)

-- | A term with two bound variables: a body in scope @S (S n)@.
data Bind2 (n :: Nat) where
    Bind2 :: Tm (S (S n)) -> Bind2 n
      deriving (Eq, Show)


------------------------------------------------------------------------
-- * Examples
------------------------------------------------------------------------

-- | Identity function: @λx. x@
ex_id :: Tm Z
ex_id = Lam (Bind1 (Var FZ))

-- | Constant function: @λx. λy. x@
ex_const :: Tm Z
ex_const = Lam (Bind1 (Lam (Bind1 (Var f1))))

-- | Function composition: @λf. λg. λx. f (g x)@
ex_comp :: Tm Z
ex_comp = Lam (Bind1 (Lam (Bind1 (Lam (Bind1
    (App (Var f2) (App (Var f1) (Var FZ))))))))

-- | Swap a pair: @λp. case p of (x, y) → (y, x)@
ex_swap :: Tm Z
ex_swap = Lam (Bind1
    (MatchPair (Var FZ)
        (Bind2 (Pair (Var f1) (Var FZ)))))

------------------------------------------------------------------------
-- * Substitution environments
------------------------------------------------------------------------

-- | A substitution environment mapping @m@ variables to terms in scope @n@.
type Env m n = Fin m -> Tm n

-- | If there are no variables in the domain, we can map to any scope
zeroE :: Env Z m
zeroE = \f -> case f of {}

-- | Extend an environment with a new term for the outermost variable.
-- @t .: env@ maps @FZ@ to @t@ and @FS x@ to @env x@.
-- Analogous to cons for lists of terms.
infixr 5 .:
(.:) :: Tm n -> Env m n -> Env (S m) n
t .: env = \f -> case f of
    FZ   -> t      -- the new outermost variable maps to t
    FS x -> env x  -- all others delegate to env

-- EXAMPLE: substitute using examples above
-- all terms must be closed and there are three of them
exampleE :: Env N3 Z
exampleE = ex_id .: ex_const .: ex_comp .: zeroE

-- EXAMPLE: an identity substitution for terms with three free 
-- variables. We map each index to a variable with that index.
id3E :: Env N3 N3
id3E = Var FZ .: Var f1 .: Var f2 .: zeroE






-- | The identity environment: maps each variable to itself.
idE :: Env n n
idE = Var

-- | The shifting environment: increments the index of every variable by one
-- i.e. weakens a scope by introducing a fresh outermost variable.
-- Apply with @applyE shift@ to weaken a term.
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
-- The new outermost variable @FZ@ maps to itself; all others are
-- shifted by one so that the result is in the extended scope.
up :: Env m n -> Env (S m) (S n)
up env = Var FZ .: applyE shift . env

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
    case mv of 
           Lam b -> eval (instantiate1 b n)
           _ -> Nothing
eval (MatchSum  e0 m m') = do
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
