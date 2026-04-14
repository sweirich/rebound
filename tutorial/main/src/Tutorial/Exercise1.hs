-- Solutions to the exercises in Lecture 1.
-- These solutions work with the hand-written infrastructure in
-- Tutorial.Scoped.Scratch; they do not require the rebound library.

module Tutorial.Exercise1 where

import Tutorial.Scoped.Scratch

------------------------------------------------------------------------
-- * Exercise 1: Example terms
------------------------------------------------------------------------

-- | First projection: λp. match p with (x, y) → x
--
-- Inside the outer Bind1: p = FZ in scope S Z.
-- Inside the Bind2:       x = FS FZ, y = FZ, p = FS (FS FZ).
-- (FS FZ is the first pair component; see instantiate2 and ex_swap.)
ex_fst :: Tm n
ex_fst = Lam (Bind1 (MatchPair (Var FZ) (Bind2 (Var (FS FZ)))))

-- | Second projection: λp. match p with (x, y) → y
ex_snd :: Tm n
ex_snd = Lam (Bind1 (MatchPair (Var FZ) (Bind2 (Var FZ))))


-- >>> eval (App ex_fst (Pair (Inj 0 Unit) (Inj 1 Unit)))
-- Just (Inj 0 Unit)

-- >>> eval (App ex_snd (Pair (Inj 0 Unit) (Inj 1 Unit)))
-- Just (Inj 1 Unit)

-- | S combinator: λf. λg. λx. f x (g x)
--
-- Inside three Bind1s: f = FS (FS FZ), g = FS FZ, x = FZ.
ex_s :: Tm Z
ex_s = Lam (Bind1 (Lam (Bind1 (Lam (Bind1
    (App (App (Var (FS (FS FZ))) (Var FZ))
         (App (Var (FS FZ))     (Var FZ))))))))

------------------------------------------------------------------------
-- * Exercise 2: Weakening
------------------------------------------------------------------------

-- | Embed a term in scope n into scope S n, leaving FZ unused.
--
-- shift :: Env m (S m) maps each x to Var (FS x), so applyE shift has
-- type Tm m -> Tm (S m).
weaken :: Tm n -> Tm (S n)
weaken = applyE shift

-- | Instantiating a weakened term recovers the original.
--
-- Proof sketch: weaken t = applyE shift t maps every variable x to
-- Var (FS x), so FZ does not appear in weaken t.  When we instantiate,
-- we apply (u .: idE) which sends FS x back to Var x, recovering t.
prop_weaken :: Tm Z -> Tm Z -> Bool
prop_weaken t u = instantiate1 (Bind1 (weaken t)) u == t

------------------------------------------------------------------------
-- * Exercise 3: Adding let
------------------------------------------------------------------------
--
-- To extend Tutorial.Scoped.Scratch with a let-expression, make these
-- three additions:
--
-- (1) New constructor in 'data Tm n':
--
--       Let :: Tm n -> Bind1 n -> Tm n
--
-- (2) New case in 'applyE' — the binder body lives in scope S m,
--     so lift the environment, exactly as for Lam:
--
--       applyE env (Let e (Bind1 b)) =
--           Let (applyE env e) (Bind1 (applyE (up env) b))
--
-- (3) New case in 'eval' — evaluate the
--     scrutinee to a value, then instantiate the body:
--
--       eval (Let e b) = eval e >>= \v -> eval (instantiate1 b v)
--
-- Let e b is call-by-value equivalent to App (Lam b) e: both evaluate
-- e to a value first and then substitute into b.

------------------------------------------------------------------------
-- * Exercise 4: Renamings
------------------------------------------------------------------------

-- | A renaming maps variables to variables (not terms).
type Ren m n = Fin m -> Fin n

-- | Lift a renaming under one binder: FZ maps to itself, FS x to FS (r x).
--
-- Unlike 'up' for substitutions, upRen does not call applyRen.
-- That is why applyRen (below) is structurally recursive — the cycle that
-- troubles Agda and Rocq does not arise.
upRen :: Ren m n -> Ren (S m) (S n)
upRen _ FZ     = FZ
upRen r (FS x) = FS (r x)

-- | Apply a renaming to a term.  Structurally recursive: no mutual recursion.
applyRen :: Ren m n -> Tm m -> Tm n
applyRen r (Var x)                 = Var (r x)
applyRen r (Lam (Bind1 b))         = Lam (Bind1 (applyRen (upRen r) b))
applyRen _ Unit                    = Unit
applyRen r (Pair a b)              = Pair (applyRen r a) (applyRen r b)
applyRen r (Inj i t)               = Inj i (applyRen r t)
applyRen r (App f a)               = App (applyRen r f) (applyRen r a)
applyRen r (MatchUnit a b)         = MatchUnit (applyRen r a) (applyRen r b)
applyRen r (MatchPair a (Bind2 b)) =
    MatchPair (applyRen r a) (Bind2 (applyRen (upRen (upRen r)) b))
applyRen r (MatchSum a (Bind1 b1) (Bind1 b2)) =
    MatchSum (applyRen r a)
             (Bind1 (applyRen (upRen r) b1))
             (Bind1 (applyRen (upRen r) b2))

-- | Every renaming r induces a substitution Var . r, and applyRen agrees
-- with applyE on that substitution.
prop_renShift :: Tm Z -> Bool
prop_renShift t = applyRen FS t == applyE shift t

------------------------------------------------------------------------
-- * Exercise 5: Alternative representation of Env
------------------------------------------------------------------------

-- | Length-indexed list.
data Vec n a where
  VNil  :: Vec Z a
  (:::) :: a -> Vec n a -> Vec (S n) a

infixr 5 :::

-- | Map over a length-indexed list.
mapVec :: (a -> b) -> Vec n a -> Vec n b
mapVec _ VNil       = VNil
mapVec f (x ::: xs) = f x ::: mapVec f xs

-- | Singleton natural numbers — needed to build idE and shiftE, which
-- must construct a list of a statically-known length at runtime.
data SNat n where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

-- | Vec-based substitution environment.
-- We use 'VEnv' to avoid clashing with the function-based 'Env' imported
-- from Tutorial.Scoped.Scratch.
type VEnv m n = Vec m (Tm n)

-- | Look up the term for a given variable index.
vApplyEnv :: VEnv m n -> Fin m -> Tm n
vApplyEnv VNil       x      = case x of {}
vApplyEnv (t ::: _)  FZ     = t
vApplyEnv (_ ::: ts) (FS x) = vApplyEnv ts x

-- | Empty environment: no variables to map.
vZeroE :: VEnv Z n
vZeroE = VNil

-- | Extend an environment: bind the outermost variable to 't'.
-- Straightforward — just cons onto the list.
vExtend :: Tm n -> VEnv m n -> VEnv (S m) n
vExtend = (:::)

-- | Identity environment: map each variable to itself.
-- Unlike the function-based 'idE = Var', this requires a runtime witness
-- of the scope because we must construct a concrete list.
vIdE :: SNat n -> VEnv n n
vIdE SZ     = VNil
vIdE (SS n) = Var FZ ::: mapVec (applyRen FS) (vIdE n)

-- | Shift environment: map each variable to the next one.
-- Also requires a runtime scope witness for the same reason.
vShiftE :: SNat n -> VEnv n (S n)
vShiftE SZ     = VNil
vShiftE (SS n) = Var (FS FZ) ::: mapVec (applyRen FS) (vShiftE n)

-- | Lift a Vec environment under one binder: FZ maps to itself, every
-- other variable x maps to (env x) weakened into the larger scope.
-- We use 'applyRen FS' (from Exercise 4) to weaken — this avoids
-- the mutual recursion that would arise from using vApplyE here.
vUp :: VEnv m n -> VEnv (S m) (S n)
vUp env = Var FZ ::: mapVec (applyRen FS) env

-- | Apply a Vec environment to a term.
-- Identical in structure to 'applyE'; the only difference is that
-- variable lookup goes through 'vApplyEnv' instead of function application.
vApplyE :: VEnv m n -> Tm m -> Tm n
vApplyE env (Var x)                          = vApplyEnv env x
vApplyE env (Lam (Bind1 b))                  = Lam (Bind1 (vApplyE (vUp env) b))
vApplyE _   Unit                             = Unit
vApplyE env (Pair a b)                       = Pair (vApplyE env a) (vApplyE env b)
vApplyE env (Inj i t)                        = Inj i (vApplyE env t)
vApplyE env (App f a)                        = App (vApplyE env f) (vApplyE env a)
vApplyE env (MatchUnit a b)                  = MatchUnit (vApplyE env a) (vApplyE env b)
vApplyE env (MatchPair a (Bind2 b))          =
    MatchPair (vApplyE env a) (Bind2 (vApplyE (vUp (vUp env)) b))
vApplyE env (MatchSum a (Bind1 b1) (Bind1 b2)) =
    MatchSum (vApplyE env a)
             (Bind1 (vApplyE (vUp env) b1))
             (Bind1 (vApplyE (vUp env) b2))

-- | Compose two Vec environments: (vComp e2 e1) maps i to e2 applied to e1(i).
-- This is the analogue of substitution composition.
vComp :: VEnv n p -> VEnv m n -> VEnv m p
vComp _  VNil       = VNil
vComp e2 (t ::: e1) = vApplyE e2 t ::: vComp e2 e1

