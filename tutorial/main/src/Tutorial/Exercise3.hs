-- Solutions to the exercises in Lecture 3.
-- These solutions use Tutorial.Scoped.Eval and
-- Tutorial.Scoped.Gen.

module Tutorial.Exercise3 where

import Data.Fin
import Data.Vec (Vec(..), (!))
import Test.QuickCheck

import qualified Tutorial.Named.Syntax   as N
import           Tutorial.Scoped.Syntax  as S
import           Tutorial.Scoped.ScopeCheck
import           Tutorial.Scoped.Gen
import           Tutorial.Scoped.Eval    
   (eval, reduce, isInert, isVal, findBranch, findBranch', Outcome(..))
import qualified Rebound.Bind.Pat as Pat

------------------------------------------------------------------------
-- * Exercise 1: Extending genTm with let
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
    let names = "x0" ::: VNil
        named  = injectTmWith names t
        scoped = projectTmWith names named
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
prop_instantiate_weaken t u = instantiate1 (bind (LocalName "x") (weaken t)) u == t

------------------------------------------------------------------------
-- * Exercise: Small-step (open) reduction
------------------------------------------------------------------------


-------------------------------------------------------------------
-- Small-step reduction
-------------------------------------------------------------------

-- | Small-step evaluation/weak-reduction
-- Returns 'Nothing' if the term cannot step
step :: Tm n -> Maybe (Tm n)
step (Var x) = Nothing
step (Lam b) = Nothing
step (App (Lam b) a) | isVal a = return (instantiate1 b a)
step (App f a)       | isInert f = do
    a' <- step a
    return (App f a')
step (App f a) = do
    f' <- step f
    return (App f' a)
step Unit = Nothing
step (Pair a1 a2) | isInert a1 = do
    a2' <- step a2
    return (Pair a1 a2')
step (Pair a1 a2) = do
    a1' <- step a1
    return (Pair a1' a2)
step (Inj i a) = do
    a' <- step a
    return (Inj i a')
step (Match e brs)
  | Right br <- findBranch' e brs = Just br
  | Just e' <- step e             = Just (Match e' brs)
  | otherwise                     = Nothing

-------------------------------------------------------------------
-- Small-step reduction properties
-------------------------------------------------------------------

-- | the step function produces a value for closed terms (NB: well-typed only)
prop_stepVal :: Tm Z -> Property
prop_stepVal e =
    let loop e =
          if isVal e then property True
          else case step e of
             Nothing ->
                counterexample ("stuck at: " ++ pp e) $
                property False
             Just e' -> loop e'
    in within 1000000 $ loop e

-- | The step function respects evaluation (NB: well-typed only. why?)
prop_evalStep :: Tm Z -> Property
prop_evalStep e =
    counterexample ("e  = " ++ pp e) $
    discardAfter 1000000 $
    case step e of
        Nothing  -> discard
        Just e'  -> counterexample ("e' = " ++ pp e') $
                    eval e == eval e'


-- | The step function respects reduce
prop_reduceStep :: Tm (S Z) -> Property
prop_reduceStep e =
    let pp' = ppWith ("x" ::: VNil) in
    counterexample ("e  = " ++ pp' e) $
    discardAfter 1000000 $
    case step e of
        Nothing  -> property (isInert e)
        Just e'  -> counterexample ("e' = " ++ pp' e') $
                    reduce e == reduce e'

------------------------------------------------------------------------
-- * Full reduction (normalization)
------------------------------------------------------------------------

-- | Full normalization: reduce everywhere, including under binders.
-- Unlike 'reduce', which leaves 'Lam' bodies untouched, 'normalize'
-- recurses into the body of every binder.
normalize :: Tm n -> Maybe (Tm n)
normalize (Var x)      = return (Var x)
normalize (Lam b)      = do
    let nm   = getPat b
        body = getBody b
    body' <- normalize body
    return (Lam (bind nm body'))
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
normalize (Match e brs) = do
    v <- normalize e
    case findBranch' v brs of
        Right body -> normalize body
        Left _   -> do
            brs' <- mapM normBranch brs
            return (Match v brs')
  where
    normBranch :: Branch n -> Maybe (Branch n)
    normBranch (Branch b) = do
            body' <- normalize (getBody b)
            return (Branch (bind (getPat b) body'))

-- | a normal term cannot reduce any further
isNormal :: Tm n -> Bool
isNormal (Var x) = True
isNormal (Lam b) = isNormal (getBody b)
isNormal (App (Lam _) u) | isVal u  = False
isNormal (App t u) = isNormal t && isNormal u
isNormal Unit = True
isNormal (Pair e1 e2) = isNormal e1 && isNormal e2
isNormal (Inj i e) = isNormal e
isNormal (Match e brs) = case findBranch' e brs of
    Left Stuck  -> all isNormalBranch brs
    Left NoMatch -> False
    Right v -> False
isNormalBranch (Branch b) = isNormal (getBody b)

{-
isNeutral :: Tm n -> Bool 
isNeutral (Var _)       = True
isNeutral (App e1 e2)   = isNeutral e1 && isNormal e2
isNeutral (Match e brs) = isNeutral e && all isNormalBranch brs
isNeutral _             = False

isNormalBranch (Branch b) = isNormal (getBody b)

-- | A term is in normal form when it contains no beta redexes anywhere,
-- including inside lambda bodies and match branches.
isNormal :: Tm n -> Bool
isNormal (Lam b)                  = isNormal (getBody b)
isNormal Unit                     = True
isNormal (Pair e1 e2)             = isNormal e1 && isNormal e2
isNormal (Inj _ e)                = isNormal e
isNormal x                        = isNeutral x
-}

-- | normalize always produces a term in full normal form.
prop_normalize_normal :: Tm Z -> Property
prop_normalize_normal t =
    discardAfter 1000000 $
    case normalize t of
        Just nf -> 
            counterexample ("nf = " ++ pp nf) $
            property (isNormal nf)
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
noRedexUnderBinder (Lam b)            = isNormal (getBody b)
noRedexUnderBinder Unit               = True
noRedexUnderBinder (Pair e1 e2)       = noRedexUnderBinder e1 && noRedexUnderBinder e2
noRedexUnderBinder (Inj _ e)          = noRedexUnderBinder e
noRedexUnderBinder (App f a)          = noRedexUnderBinder f && noRedexUnderBinder a
noRedexUnderBinder (Match e brs) = noRedexUnderBinder e && 
   all (\(Branch b) -> isNormal (getBody b)) brs



testAll :: IO ()
testAll = do
    let args = stdArgs { maxSuccess = 100000 }
    putStrLn "prop_stepVal:"               
    quickCheckWith args (forAll0 Typed Full prop_stepVal)
    putStrLn "prop_evalStep:"             
    quickCheckWith args (forAll0 Typed Full prop_evalStep)
    putStrLn "prop_reduceStep:"            
    quickCheckWith args (forAll1 Scoped Full prop_reduceStep)

    putStrLn "normalize/normal closed"     
    quickCheckWith args (forAll0 Scoped Full (prop_normalize_normal ))
    -- putStrLn "normalize/normal open"       
    -- quickCheckWith args (forAll1 Scoped Full (prop_normalize_normal  @(S Z)))
    putStrLn "normalize/idempotent closed"     
    quickCheckWith args (forAll0 Scoped Full (prop_normalize_idempotent @Z))
    putStrLn "normalize/idempotent open"       
    quickCheckWith args (forAll1 Scoped Full (prop_normalize_idempotent @(S Z)))
    putStrLn "normalize/eval"              
    quickCheckWith args (forAll0 Scoped Full prop_normalize_eval)
    putStrLn "normalize/reduce closed"         
    quickCheckWith args (forAll0 Typed Full (prop_normalize_reduce  @Z))
    putStrLn "normalize/reduce open"           
    quickCheckWith args (forAll1 Typed Full (prop_normalize_reduce  @(S Z)))