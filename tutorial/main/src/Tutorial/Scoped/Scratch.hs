-- Module      : Scoped.Scratch
-- Description : Complete definitions of well-scoped de Bruijn term representations from scratch.

module Tutorial.Scoped.Scratch where

------------------------------------------------------------------------
-- * Finite sets
------------------------------------------------------------------------

-- | Unary natural numbers, used as type-level scopes.
-- A term in scope @n@ has variables @0 .. n-1@.
data Nat = Z | S Nat

-- | @Fin n@ is the type of de Bruijn indices in scope @n@:
-- the finite set @{0, 1, ..., n-1}@.
-- @FZ@ represents @0@, and @FS x@ represents @x + 1@.
data Fin n where
    FZ :: Fin (S n)
    FS :: Fin n -> Fin (S n)

deriving instance (Eq (Fin n))
deriving instance (Show (Fin n))

------------------------------------------------------------------------
-- * Substitution environments
------------------------------------------------------------------------

-- | A substitution environment mapping @m@ variables to terms in scope @n@.
type Env m n = Fin m -> Tm n

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

-- | The identity environment: maps each variable to itself.
idE :: Env n n
idE = Var

-- | The shifting environment: maps each variable @x@ to @Var (FS x)@,
-- i.e. weakens a scope by introducing a fresh outermost variable.
-- Apply with @applyE shift@ to weaken a term.
shift :: Env m (S m)
shift = Var . FS

-- | Lift an environment under one binder.
-- The new outermost variable @FZ@ maps to itself; all others are
-- shifted by one so that the result lives in the extended scope.
lift :: Env m n -> Env (S m) (S n)
lift env = Var FZ .: (applyE shift . env)

-- | Compose two environments: first apply @g@ to get an intermediate term,
-- then substitute that term using @f@.
-- Satisfies @applyE (compE f g) = applyE f . applyE g@.
compE :: Env m n -> Env l m -> Env l n
compE f g x = applyE f (g x)

------------------------------------------------------------------------
-- * Binders and instantiation
------------------------------------------------------------------------

-- | A term with one bound variable: a body in scope @S n@ packaged
-- so that the binder is not visible outside.
data Bind1 n where
    Bind1 :: Tm (S n) -> Bind1 n
      deriving (Eq, Show)

-- | A term with two bound variables: a body in scope @S (S n)@.
data Bind2 (n :: Nat) where
    Bind2 :: Tm (S (S n)) -> Bind2 n
      deriving (Eq, Show)

-- | Open a single-variable binder by substituting @t@ for the bound variable.
instantiate1 :: Bind1 n -> Tm n -> Tm n
instantiate1 (Bind1 body) t = applyE (t .: idE) body

-- | Open a two-variable binder by substituting @t1@ and @t2@ for the
-- two bound variables (outermost first).
instantiate2 :: Bind2 n -> Tm n -> Tm n -> Tm n
instantiate2 (Bind2 body) t1 t2 = applyE (t1 .: t2 .: idE) body

------------------------------------------------------------------------
-- * Types, terms, and substitution
------------------------------------------------------------------------

data Ty = One | Zero | Ty :-> Ty | Ty :* Ty | Ty :+ Ty
  deriving (Eq, Show)

data Tm n where
    Var   :: Fin n -> Tm n
    Lam   :: Bind1 n -> Tm n
    Unit  :: Tm n
    Pair  :: Tm n -> Tm n -> Tm n
    Inj   :: Int -> Tm n -> Tm n
    -- elimination forms for functions (negative values)
    App   :: Tm n -> Tm n -> Tm n
    -- elimination forms for positive values
    MatchUnit :: Tm n -> Tm n -> Tm n
    MatchPair :: Tm n -> Bind2 n -> Tm n
    MatchSum  :: Tm n -> Bind1 n -> Bind1 n -> Tm n
      deriving (Eq, Show)

-- | Apply a substitution environment to a term, replacing every free
-- variable @x@ with @env x@.  The environment is lifted under each
-- binder so that bound variables are not modified.
applyE :: Env m n -> Tm m -> Tm n
applyE env (Var x)              = env x
applyE env (Lam (Bind1 b))      = Lam (Bind1 (applyE (lift env) b))
applyE _   Unit                 = Unit
applyE env (Pair a b)           = Pair (applyE env a) (applyE env b)
applyE env (Inj i t)            = Inj i (applyE env t)
applyE env (App f a)            = App (applyE env f) (applyE env a)
applyE env (MatchUnit a b)      = MatchUnit (applyE env a) (applyE env b)
applyE env (MatchPair a (Bind2 b)) =
    MatchPair (applyE env a) (Bind2 (applyE (lift (lift env)) b))
applyE env (MatchSum a (Bind1 b1) (Bind1 b2)) =
    MatchSum (applyE env a) (Bind1 (applyE (lift env) b1)) (Bind1 (applyE (lift env) b2))


------------------------------------------------------------------------
-- * Examples
------------------------------------------------------------------------

-- | Identity function: @λx. x@
ex_id :: Tm Z
ex_id = Lam (Bind1 (Var FZ))

-- | Constant function: @λx. λy. x@
ex_const :: Tm Z
ex_const = Lam (Bind1 (Lam (Bind1 (Var (FS FZ)))))

-- | Function composition: @λf. λg. λx. f (g x)@
ex_comp :: Tm Z
ex_comp = Lam (Bind1 (Lam (Bind1 (Lam (Bind1
    (App (Var (FS (FS FZ))) (App (Var (FS FZ)) (Var FZ))))))))

-- | Swap a pair: @λp. match p with (x, y) → (y, x)@
-- In the @Bind2@ body, @FZ@ is the first component and @FS FZ@ is the second.
ex_swap :: Tm Z
ex_swap = Lam (Bind1
    (MatchPair (Var FZ)
        (Bind2 (Pair (Var (FS FZ)) (Var FZ)))))


------------------------------------------------------------------------
-- * Evaluator
------------------------------------------------------------------------

-- | (big-step) evaluation function 
eval :: Tm Z -> Maybe (Tm Z)
eval (Var x)      = case x of {}
eval (Lam m)      = return (Lam m)
eval Unit         = return Unit
eval (Pair e1 e2) = Pair <$> eval e1 <*> eval e2
eval (Inj i m) = do
    t <- eval m
    return (Inj i t)
eval (App m n) = do 
    mv <- eval m
    nv <- eval n 
    case mv of 
           Lam n -> eval (instantiate1 n nv)
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
