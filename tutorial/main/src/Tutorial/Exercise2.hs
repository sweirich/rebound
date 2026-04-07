-- Solutions to the exercises in Lecture 2.
-- These solutions use Tutorial.Scoped.ScopeCheck and
-- Tutorial.Scoped.Gen.

module Tutorial.Exercise2 where

import Data.Fin
import Data.Vec (Vec(..), (!))
import Test.QuickCheck

import qualified Tutorial.Named.Syntax   as N
import           Tutorial.Scoped.Syntax  as S
import           Tutorial.Scoped.ScopeCheck
import           Tutorial.Scoped.Gen
import           Tutorial.Scoped.Eval    (eval, reduce, isInert, isVal)

------------------------------------------------------------------------
-- * Exercise 1: Tracing projectTmWith
------------------------------------------------------------------------
--
-- Trace 1: projectTm (N.Lam "x" (N.Lam "y" (N.Var "x")))
--
-- Call 1: projectTmWith [] (N.Lam "x" (N.Lam "y" (N.Var "x")))
--   → extend scope: vs = [("x", FZ)]
--
-- Call 2: projectTmWith [("x", FZ)] (N.Lam "y" (N.Var "x"))
--   → extend scope: vs = [("y", FZ), ("x", FS FZ)]
--     (every existing entry gets its index shifted up by FS)
--
-- Call 3: projectTmWith [("y", FZ), ("x", FS FZ)] (N.Var "x")
--   → lookup "x" finds FS FZ
--   → return S.Var (FS FZ)
--
-- Assembling back up:
--   inner Lam body = S.Var (FS FZ) :: S.Tm (S (S Z))
--   outer Lam body = S.Lam (S.bind1 (S.LocalName "y") (S.Var (FS FZ))) :: S.Tm (S Z)
--   result         = S.Lam (S.bind1 (S.LocalName "x") (...))            :: S.Tm Z


ex1_result1 :: Either ScopeCheckError (S.Tm Z)
ex1_result1 = projectTm (N.Lam "x" (N.Lam "y" (N.Var "x")))

-- >>> ex1_result1
-- Right (Lam (bind1 (Lam (bind1 (Var 1)))))


-- The expected de Bruijn term:
--   λ. λ. 1          (x is one binder away)
ex1_expected1 :: S.Tm Z
ex1_expected1 = S.Lam (S.bind1 (S.LocalName "x")
                  (S.Lam (S.bind1 (S.LocalName "y")
                    (S.Var (FS FZ)))))

-- >>> ex1_expected1
-- Lam (bind1 (Lam (bind1 (Var 1))))

-- Verify:
ex1_check1 :: Bool
ex1_check1 = ex1_result1 == Right ex1_expected1

-- >>> ex1_check1
-- True

-- ---------------------------------------------------------------------------
--
-- Trace 2: projectTm (N.Case (N.Var "p") [(N.Pair [N.Var "x", N.Var "y"], N.Var "x")])
--
-- This matches the MatchPair case in projectTmWith:
--   case e of { (v1, v2) -> body }
--   where v1 = "x", v2 = "y"
--
-- The rule (from ScopeCheck.hs):
--   b' <- projectTmWith ((v2, FZ) : (v1, FS FZ) : map (fmap (FS . FS)) vs) e1
--
-- So inside the body:
--   vs = [("y", FZ), ("x", FS FZ), ("p", FS (FS FZ))]
--   "y" maps to FZ  (second component, innermost)
--   "x" maps to FS FZ (first component)
--
-- Looking up "x" in the body gives FS FZ.
--
-- Answer: "y" maps to FZ; "x" maps to FS FZ.
-- The convention matches instantiate2 in Eval.hs:
--   instantiate2 bnd v1 v2 maps FS FZ → v1 (first component) and FZ → v2 ...

ex1_result2 :: Either ScopeCheckError (S.Tm Z)
ex1_result2 = projectTm
    (N.Case (N.Var "p")
        [(N.Pair [N.Var "x", N.Var "y"], N.Var "x")])

-- >>> ex1_result2
-- Left (UnboundVariable "p")


-- With "p" in scope (scope S Z):
ex1_result2_open :: Either ScopeCheckError (S.Tm (S Z))
ex1_result2_open = projectTmWith [("p", FZ)]
    (N.Case (N.Var "p")
        [(N.Pair [N.Var "x", N.Var "y"], N.Var "x")])

-- >>> ex1_result2_open
-- Right (MatchPair (Var 0) (bind2 (Var 1)))

------------------------------------------------------------------------
-- * Exercise 2: Extending the conversions with let
------------------------------------------------------------------------
--
-- The named representation already encodes let as syntactic sugar:
--   letTm x rhs body = App (Lam x body) rhs
-- So projectTmWith and injectTmWith handle let-expressions automatically
-- through the existing Lam and App cases — no new constructor is needed
-- in N.Tm.
--
-- If we were to add a dedicated S.Let constructor to S.Tm:
--
--   Let :: Tm n -> Bind1 Tm Tm n -> Tm n
--
-- then the new cases would be:
--
-- projectTmWith vs (N.Let v e b) = do
--     e' <- projectTmWith vs e
--     b' <- projectTmWith ((v, FZ) : map (fmap FS) vs) b
--     return $ S.Let e' (S.bind1 (S.LocalName v) b')
--
-- injectTmWith vs (S.Let e b) =
--     N.Let s (injectTmWith vs e) (injectTmWith (s ::: vs) (S.getBody1 b))
--     where s = freshen (show (S.getLocalName b)) vs
--
-- The treatment is identical to Lam in both directions:
--   - project: extend the scope with the bound name (FZ) and shift existing
--     names by FS, exactly as for Lam.
--   - inject: retrieve the stored LocalName hint, freshen it against the
--     current vector, and prepend it before recursing into the body.
-- The only difference is that Let also carries a scrutinee `e` that is
-- translated in the *current* scope (not the extended one), just as in App.
--
-- prop_project_round_trip continues to hold because injectTm produces a
-- named term whose let-binder carries the same LocalName stored by bind1,
-- and projectTmWith assigns the bound variable FZ again, recovering the
-- original de Bruijn term.

------------------------------------------------------------------------
-- * Exercise 3: LocalName and α-equivalence
------------------------------------------------------------------------

-- (a) The trivial Eq instance
--
-- S.Lam (S.bind1 (S.LocalName "x") (S.Var FZ))
--   == S.Lam (S.bind1 (S.LocalName "y") (S.Var FZ))
-- evaluates to True.
--
-- The Eq instance for Bind1 compares the bodies after applying any pending
-- substitution.  The bodies are both S.Var FZ, which are structurally
-- equal.  The stored LocalName values are compared with the trivial Eq
-- instance (which always returns True), so the names play no role.
-- This gives the correct notion of α-equivalence: λx.x and λy.y are equal.

test_alpha_equiv :: Bool
test_alpha_equiv =
    S.Lam (S.bind1 (S.LocalName "x") (S.Var FZ))
      ==
    S.Lam (S.bind1 (S.LocalName "y") (S.Var FZ))

-- >>> test_alpha_equiv
-- True

-- (b) Failing term if LocalName had a real Eq instance
--
-- Consider the term with two nested binders sharing the name "x":
ex3b_term :: S.Tm Z
ex3b_term = S.Lam (S.bind1 (S.LocalName "x")
              (S.Lam (S.bind1 (S.LocalName "x")
                (S.Var FZ))))
-- λ x. λ x. x   (inner x)

-- injectTm ex3b_term:
--   outer binder: hint = "x", vs = VNil          → s = "x"
--   inner binder: hint = "x", vs = "x" ::: VNil  → freshen produces "x0"
--   body: Var FZ → "x0"
--   Named form: N.Lam "x" (N.Lam "x0" (N.Var "x0"))

-- projectTm of that named form:
--   inner binder stored as bind1 (LocalName "x0") (Var FZ)
--   original inner binder was  bind1 (LocalName "x")  (Var FZ)
--
-- With the trivial Eq:   LocalName "x0" == LocalName "x"  → True  ✓
-- With a real Eq:        LocalName "x0" /= LocalName "x"  → False ✗
--   prop_project_round_trip would fail on ex3b_term.

ex3b_inject :: N.Tm
ex3b_inject = injectTm ex3b_term
-- N.Lam "x" (N.Lam "x0" (N.Var "x0"))

ex3b_project :: Either ScopeCheckError (S.Tm Z)
ex3b_project = projectTm ex3b_inject
-- Right (Lam (bind1 "x" (Lam (bind1 "x0" (Var FZ)))))
-- Equal to ex3b_term under the trivial Eq (name hints are ignored).

-- (c) Example where freshen fires
--
-- Term: Lam (bind1 (LocalName "x") (Lam (bind1 (LocalName "x") (Var FZ))))
-- (same as ex3b_term above)
--
-- injectTmWith VNil:
--   1. Outer binder: hint "x", vs = VNil
--      inVec "x" VNil = False  →  s = "x"
--      Recurse with vs = "x" ::: VNil
--   2. Inner binder: hint "x", vs = "x" ::: VNil
--      inVec "x" ("x" ::: VNil) = True  →  try "x0"
--      inVec "x0" ("x" ::: VNil) = False  →  s = "x0"
--      Recurse with vs = "x0" ::: "x" ::: VNil
--   3. Var FZ: vs ! FZ = "x0"
--
-- Result: N.Lam "x" (N.Lam "x0" (N.Var "x0"))

------------------------------------------------------------------------
-- * Exercise 4: Extending genTm with let
------------------------------------------------------------------------
--
-- After adding Let :: Tm n -> Bind1 Tm Tm n -> Tm n to S.Tm, extend
-- genScopedTm in Tutorial.Scoped.Gen by adding to the Full branch:
--
--   , Let <$> gen <*> gen1
--
-- where gen1 = bind1 @Tm <$> genLocalName <*> genTm l (next n) sz'
-- is already computed for the Lam and MatchSum cases.
--
-- Why gen1 is right:
--   Let e b   has e :: Tm n  (scrutinee, current scope)
--             and b :: Bind1 Tm Tm n  (body under one new binder, scope S n)
--   gen1 generates exactly a Bind1 whose body lives in scope S n.
--   This is the same reason gen1 is used for Lam.
--
-- How Let differs from App:
--   App f a  — both subterms run in the same scope n.
--   Let e b  — scrutinee e runs in scope n; body of b runs in scope S n.
--   The binder introduces one fresh variable FZ visible only inside b.
--
-- prop_project_round_trip still passes after this change because:
--   1. injectTm (Let e b) = N.letTm s (injectTm e) (injectTmWith (s ::: vs) body)
--      which is App (Lam s body') e', fully handled by existing cases.
--   2. projectTm of that named form reconstructs Let e' b' with the same
--      de Bruijn structure, and LocalName equality ignores the freshened name.

------------------------------------------------------------------------
-- * Exercise 5: Open-term round trip
------------------------------------------------------------------------

-- The free variable is named "x0" to match the convention in injectTmWith
-- (just any string will do; see note below).

-- | Round-trip property for terms with one free variable.
--
-- We supply a name "x0" for the single free variable:
--   injectTmWith ("x0" ::: VNil) t   names index FZ as "x0"
--   projectTmWith [("x0", FZ)]        maps "x0" back to FZ
--
-- The choice of name does not matter for correctness: whatever string we
-- use, injectTmWith will emit that string for every occurrence of Var FZ,
-- and projectTmWith will map it back to FZ.  The only requirement is that
-- the same name is used in both calls.
prop_project_round_trip_open :: S.Tm (S Z) -> Bool
prop_project_round_trip_open t =
    let freeVarName = "x0"
        named  = injectTmWith (freeVarName ::: VNil) t
        scoped = projectTmWith [(freeVarName, FZ)] named
    in scoped == Right t


------------------------------------------------------------------------
-- * Exercise 5: Substitution laws
------------------------------------------------------------------------

-- | Identity law: applying the identity substitution is a no-op.
prop_idE :: Property
prop_idE = forAll0 Scoped Full $ \t -> applyE @Tm idE t == t

-- | Identity law for open terms (where variables can actually occur).
prop_idE_open :: Property
prop_idE_open = forAll1 Scoped Full $ \t -> applyE @Tm idE t == t

-- | Composition law: applying f after g equals applying compE f g directly.
-- We test with a concrete environment g that closes the one free variable.
-- compE requires the types to line up: g :: Env (S Z) Z,  f :: Env Z Z.
prop_compE :: Property
prop_compE = 
    forAll0 Scoped Full $ \u0 ->
    forAll1 Scoped Full $ \u1 ->
    forAll1 Scoped Full $ \t ->
    let g :: Env Tm N1 N1 
        g = u1 .: zeroE    
        f :: Env Tm N1 N0 
        f = u0 .: idE      
    in applyE f (applyE g t) == applyE (g .>> f) t

weaken :: Tm n -> Tm (S n)
weaken = applyE @Tm shift1E

-- | Instantiate-shift round-trip: instantiating a weakened term is identity.
prop_instantiate_weaken :: Tm Z -> Tm Z -> Bool
prop_instantiate_weaken t u = instantiate1 (bind1 (LocalName "x") (weaken t)) u == t

------------------------------------------------------------------------
-- * Exercise 8: Full reduction (normalization)
------------------------------------------------------------------------

-- | Full normalization: reduce everywhere, including under binders.
-- Unlike 'reduce', which leaves 'Lam' bodies untouched, 'normalize'
-- recurses into the body of every binder.
normalize :: Tm n -> Maybe (Tm n)
normalize (Var x)      = return (Var x)
normalize (Lam b)      = do
    let nm   = getLocalName b
        body = getBody1 b
    body' <- normalize body
    return (Lam (bind1 nm body'))
normalize Unit         = return Unit
normalize (Pair e1 e2) = do
    v1 <- normalize e1
    v2 <- normalize e2
    return (Pair v1 v2)
normalize (Inj i m) = do
    t <- normalize m
    return (Inj i t)
normalize (App m n) = do
    mv <- normalize m
    nv <- normalize n
    case mv of
        Lam b | isVal nv -> normalize (instantiate1 b nv)
        _                -> return (App mv nv)
normalize (MatchSum e0 m m') = do
    v <- normalize e0
    case v of
        Inj 0 v1 | isVal v1 -> normalize (instantiate1 m v1)
        Inj 1 v1 | isVal v1 -> normalize (instantiate1 m' v1)
        _ -> do
            let nm    = getLocalName m
                body1 = getBody1 m
                nm'   = getLocalName m'
                body2 = getBody1 m'
            b1 <- normalize body1
            b2 <- normalize body2
            return (MatchSum v (bind1 nm b1) (bind1 nm' b2))
normalize (MatchPair e m) = do
    v <- normalize e
    case v of
        Pair v1 v2 | isVal v -> normalize (instantiate2 m v2 v1)
        _ -> do
            let nms  = getLocalName2 m
                nm1  = nms ! FZ
                nm2  = nms ! FS FZ
                body = getBody2 m
            body' <- normalize body
            return (MatchPair v (bind2 nm1 nm2 body'))
normalize (MatchUnit e m) = do
    v <- normalize e
    case v of
        _ | isVal v -> normalize m
        _           -> do
            m' <- normalize m
            return (MatchUnit v m')

-- | A term is in full normal form when it contains no beta redexes anywhere,
-- including inside lambda bodies and match branches.
isNormal :: Tm n -> Bool
isNormal (Var _)                  = True
isNormal (Lam b)                  = isNormal (getBody1 b)
isNormal Unit                     = True
isNormal (Pair e1 e2)             = isNormal e1 && isNormal e2
isNormal (Inj _ e)                = isNormal e
isNormal (App (Lam _) a)          | isVal a  = False   -- CBV beta redex
isNormal (App f a)                = isNormal f && isNormal a
isNormal (MatchUnit e _)          | isVal e  = False   -- CBV matchunit redex
isNormal (MatchUnit e m)          = isNormal e && isNormal m
isNormal (MatchPair p@(Pair _ _) _) | isVal p = False   -- CBV matchpair redex
isNormal (MatchPair e b)          = isNormal e && isNormal (getBody2 b)
isNormal (MatchSum (Inj _ v) _ _) | isVal v  = False   -- CBV matchsum redex
isNormal (MatchSum e b1 b2)       = isNormal e
                                 && isNormal (getBody1 b1)
                                 && isNormal (getBody1 b2)

-- | normalize always produces a term in full normal form.
prop_normalize_normal :: forall n. SNatI n => Tm n -> Property
prop_normalize_normal t =
    discardAfter 1000000 $
    case normalize t of
        Just nf -> property (isNormal nf)
        Nothing -> discard

-- | normalize is idempotent: normalizing an already-normal term is a no-op.
prop_normalize_idempotent :: forall n. SNatI n => Tm n -> Property
prop_normalize_idempotent t =
    discardAfter 1000000 $
    case normalize t of
        Just nf -> normalize nf === Just nf
        Nothing -> discard

-- | On well-typed closed terms, normalize succeeds whenever eval does, and its
-- result is in normal form.  On well-scoped (possibly ill-typed) terms,
-- normalize can succeed even when eval fails (type errors cause eval to return
-- Nothing but normalize still returns Just).
prop_normalize_eval :: Tm Z -> Property
prop_normalize_eval t =
    discardAfter 1000000 $
    counterexample ("term: " ++ pp t) $
    case eval t of
        Just v  -> counterexample ("eval: " ++ pp v) $
                   case normalize t of
                       Just nf -> counterexample ("normalize: " ++ pp nf) $
                                  property (isNormal nf)
                       Nothing -> property False
        Nothing -> discard

-- | When there is no redex hiding inside a lambda body or match branch,
-- normalize and reduce produce the same result.
-- We classify how often this condition holds in the generated test suite.
prop_normalize_reduce :: forall n. SNatI n => Tm n -> Property
prop_normalize_reduce t =
    discardAfter 1000000 $
    classify (noRedexUnderBinder t) "no redex under binder" $
    case (reduce t, normalize t) of
        (Just v, Just nf) | noRedexUnderBinder t -> v === nf
        _                                         -> property True

-- | Holds when no beta redex appears strictly inside a binder body.
-- Outside binders the term may still have redexes; those are handled
-- identically by both 'reduce' and 'normalize'.
noRedexUnderBinder :: Tm n -> Bool
noRedexUnderBinder (Var _)            = True
noRedexUnderBinder (Lam b)            = isNormal (getBody1 b)
noRedexUnderBinder Unit               = True
noRedexUnderBinder (Pair e1 e2)       = noRedexUnderBinder e1 && noRedexUnderBinder e2
noRedexUnderBinder (Inj _ e)          = noRedexUnderBinder e
noRedexUnderBinder (App f a)          = noRedexUnderBinder f && noRedexUnderBinder a
noRedexUnderBinder (MatchUnit e m)    = noRedexUnderBinder e && noRedexUnderBinder m
noRedexUnderBinder (MatchPair e b)    = noRedexUnderBinder e && isNormal (getBody2 b)
noRedexUnderBinder (MatchSum e b1 b2) = noRedexUnderBinder e
                                     && isNormal (getBody1 b1)
                                     && isNormal (getBody1 b2)
