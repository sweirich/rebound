-- Solutions to the exercises in Lecture 1.
-- These solutions work with the hand-written infrastructure in
-- Tutorial.Scoped.Scratch; they do not require the rebound library.

module Tutorial.Scoped.Solutions where

import Tutorial.Scoped.Scratch
import Test.QuickCheck

------------------------------------------------------------------------
-- * Exercise 1: Example terms
------------------------------------------------------------------------

-- | First projection: λp. match p with (x, y) → x
--
-- Inside the outer Bind1: p = FZ in scope S Z.
-- Inside the Bind2:       x = FZ, y = FS FZ, p = FS (FS FZ).
-- (FZ is the first pair component; see instantiate2 and ex_swap.)
ex_fst :: Tm Z
ex_fst = Lam (Bind1 (MatchPair (Var FZ) (Bind2 (Var FZ))))

-- | Second projection: λp. match p with (x, y) → y
ex_snd :: Tm Z
ex_snd = Lam (Bind1 (MatchPair (Var FZ) (Bind2 (Var (FS FZ)))))

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
-- (3) New case in 'eval' in Tutorial.Scoped.Eval — evaluate the
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
-- Unlike 'lift' for substitutions, liftRen does not call applyRen.
-- That is why applyRen (below) is structurally recursive — the cycle that
-- troubles Agda and Rocq does not arise.
liftRen :: Ren m n -> Ren (S m) (S n)
liftRen _ FZ     = FZ
liftRen r (FS x) = FS (r x)

-- | Apply a renaming to a term.  Structurally recursive: no mutual recursion.
applyRen :: Ren m n -> Tm m -> Tm n
applyRen r (Var x)                 = Var (r x)
applyRen r (Lam (Bind1 b))         = Lam (Bind1 (applyRen (liftRen r) b))
applyRen _ Unit                    = Unit
applyRen r (Pair a b)              = Pair (applyRen r a) (applyRen r b)
applyRen r (Inj i t)               = Inj i (applyRen r t)
applyRen r (App f a)               = App (applyRen r f) (applyRen r a)
applyRen r (MatchUnit a b)         = MatchUnit (applyRen r a) (applyRen r b)
applyRen r (MatchPair a (Bind2 b)) =
    MatchPair (applyRen r a) (Bind2 (applyRen (liftRen (liftRen r)) b))
applyRen r (MatchSum a (Bind1 b1) (Bind1 b2)) =
    MatchSum (applyRen r a)
             (Bind1 (applyRen (liftRen r) b1))
             (Bind1 (applyRen (liftRen r) b2))

-- | Every renaming r induces a substitution Var . r, and applyRen agrees
-- with applyE on that substitution.
prop_renShift :: Tm Z -> Bool
prop_renShift t = applyRen FS t == applyE shift t

------------------------------------------------------------------------
-- * Exercise 5: Substitution laws
------------------------------------------------------------------------
--
-- For Tm Z (closed terms) there are no free variables, so the identity
-- and composition laws hold trivially.  The interesting cases arise in
-- Tm (S Z) and larger.  To test those with QuickCheck we need an
-- Arbitrary instance; a minimal one is given below.

-- | Singleton natural numbers (needed to parameterise the generator).
data SNat n where
    SZ :: SNat Z
    SS :: SNat n -> SNat (S n)

-- | Generate a random term in scope n.
genTm :: SNat n -> Int -> Gen (Tm n)
genTm sn sz = case sn of
    SZ ->
        if sz <= 0 then pure Unit
        else oneof $ closedGens sn sz
    SS _ ->
        if sz <= 0 then oneof [Var <$> genFin sn, pure Unit]
        else oneof $ (Var <$> genFin sn) : closedGens sn sz
  where
    sz' = sz `div` 2
    closedGens :: SNat n -> Int -> [Gen (Tm n)]
    closedGens sn' s =
        [ pure Unit
        , Lam . Bind1 <$> genTm (SS sn') s'
        , App  <$> genTm sn' s' <*> genTm sn' s'
        , Pair <$> genTm sn' s' <*> genTm sn' s'
        , Inj  <$> elements [0,1] <*> genTm sn' s'
        ]
      where s' = s `div` 2

genFin :: SNat (S n) -> Gen (Fin (S n))
genFin (SS SZ)    = pure FZ
genFin (SS sn'@(SS _)) = oneof [pure FZ, FS <$> genFin sn']

instance Arbitrary (Tm Z) where
    arbitrary = sized (genTm SZ)

-- A newtype for terms with one free variable, so we can give a separate
-- Arbitrary instance without an overlapping instance.
newtype Tm1 = Tm1 { unTm1 :: Tm (S Z) }
    deriving (Eq, Show)

instance Arbitrary Tm1 where
    arbitrary = Tm1 <$> sized (genTm (SS SZ))

-- | Identity law: applying the identity substitution is a no-op.
prop_idE :: Tm Z -> Bool
prop_idE t = applyE idE t == t

-- | Identity law for open terms (where variables can actually occur).
prop_idE_open :: Tm1 -> Bool
prop_idE_open (Tm1 t) = applyE idE t == t

-- | Composition law: applying f after g equals applying compE f g directly.
--
-- We test with a concrete environment g that closes the one free variable.
-- compE requires the types to line up: g :: Env (S Z) Z,  f :: Env Z Z.
prop_compE :: Tm1 -> Bool
prop_compE (Tm1 t) =
    let g = Unit .: idE   -- Env (S Z) Z: substitute Unit for the free variable
        f = idE           -- Env Z Z
    in applyE f (applyE g t) == applyE (compE f g) t

-- | Instantiate-shift round-trip: instantiating a weakened term is identity.
prop_instantiate_weaken :: Tm Z -> Tm Z -> Bool
prop_instantiate_weaken t u = instantiate1 (Bind1 (weaken t)) u == t
