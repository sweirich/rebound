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
--           Let (applyE env e) (Bind1 (applyE (lift env) b))
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
-- Unlike 'up' for substitutions, liftRen does not call applyRen.
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

