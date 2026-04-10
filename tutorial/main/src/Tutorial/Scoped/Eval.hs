{-|
Module      : Tutorial.Scoped.Eval
Description : Evaluation for the scoped lambda calculus
-}

module Tutorial.Scoped.Eval where

import Tutorial.Scoped.Syntax
import qualified Rebound.Bind.Pat as Pat
import Tutorial.Scoped.Gen
import Test.QuickCheck
import Tutorial.Scoped.ScopeCheck
import Data.Fin

-------------------------------------------------------------------
-- Evaluator
-------------------------------------------------------------------

-- | (big-step) evaluation function
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
           Lam n -> eval (instantiate1 n nv)
           _ -> Nothing
eval (Match e brs) = do
    v <- eval e
    br <- findBranch v brs 
    eval br

-------------------------------------------------------------------
-- Pattern matching
-------------------------------------------------------------------

-- | Compare a pattern against a value, returning an environment binding
-- the pattern variables (if the pattern matches)
patternMatch :: Pat m -> Tm n -> Maybe (Env Tm m n)
patternMatch (PVar _) v | isVal v     = Just (oneE v)
patternMatch PUnit Unit               = Just zeroE
patternMatch (PPair p1 p2) (Pair v1 v2) = do
    env1 <- patternMatch p1 v1
    env2 <- patternMatch p2 v2    
    withSNat (size p2) $ return (env2 .++ env1)
patternMatch (PInj i p) (Inj j v) | i == j = patternMatch p v
patternMatch _ _ = Nothing

-- | Find the first branch whose pattern matches the scrutinee and
-- instantiate its body.
findBranch :: Tm n -> [Branch n] -> Maybe (Tm n)
findBranch _ [] = Nothing
findBranch e (Branch b : rest) =
    case patternMatch (Pat.getPat b) e of
        Just r  -> Just (Pat.instantiate b r)
        Nothing -> findBranch e rest

-- | is a term a value?
-- Note: values are closed under substitution by values
isVal :: Tm n -> Bool
isVal (Var x) = True
isVal (Lam b) = True
isVal Unit = True
isVal (Inj i e) = isVal e
isVal (Pair e1 e2) = isVal e1 && isVal e2
isVal e = False

-------------------------------------------------------------------
-- Properties of `eval`
-------------------------------------------------------------------

-- if a term evaluates, it produces a value
prop_evalVal :: Tm Z -> Property
prop_evalVal = \t ->
    counterexample ("term: " ++ pp t) $
    discardAfter 10000 $
    case eval t of
        Just v ->
            counterexample ("not a value: " ++ pp v) $
            property (isVal v)
        Nothing ->
            discard

-- all terms produce values (NB: this holds for well-typed terms only!)
prop_eval_exists_Val :: Tm Z -> Property
prop_eval_exists_Val = \t ->
    counterexample ("term: " ++ pp t) $
    discardAfter 10000 $
    case eval t of
        Just v ->
            counterexample ("not a value: " ++ pp v) $
            property (isVal v)
        Nothing ->
            counterexample ("doesn't eval") $
            property False

-------------------------------------------------------------------
-- CBV weak reduction for open terms
-------------------------------------------------------------------

-- | weak *call-by-value* reduction
-- only beta-reduce if the argument is a value
-- do not reduce under lambda terms
-- returns 'Nothing' if the term is inert
-- (i.e. has been reduced as far as possible)

reduce :: Tm n -> Maybe (Tm n)
reduce (Var x)      = return (Var x)
reduce (Lam m)      = return (Lam m)
reduce Unit         = return Unit
reduce (Pair e1 e2) = do
    v1 <- reduce e1
    v2 <- reduce e2
    return (Pair v1 v2)
reduce (Inj i m) = do
    t <- reduce m
    return (Inj i t)
reduce (App m n) = do
    mv <- reduce m
    nv <- reduce n
    case mv of
           Lam n | isVal nv   -> reduce (instantiate1 n nv)
           _     | isInert mv -> return (App mv nv)
           _                  -> Nothing
reduce (Match e brs) = do
    v <- reduce e
    case findBranch v brs of
        Just br                 -> reduce br
        Nothing | isInert v     -> return (Match v brs)
                | otherwise     -> Nothing

-- | an inert term cannot reduce any further
isInert :: Tm n -> Bool
isInert (Var x) = True
isInert (Lam b) = True
isInert (App (Lam _) u) | isVal u  = False
isInert (App t u) = isInert t && isInert u
isInert Unit = True
isInert (Pair e1 e2) = isInert e1 && isInert e2
isInert (Inj i e) = isInert e
isInert (Match e brs) = case findBranch e brs of
    Just _  -> False
    Nothing -> isInert e

-------------------------------------------------------------------
-- Properties of 'reduce'
-------------------------------------------------------------------

-- | If reduce produces a term, it is inert
prop_reduce_inert :: forall n. SNatI n => Tm n -> Property
prop_reduce_inert t =
    discardAfter 1000000 $
    case reduce t of
        Just v -> property (isInert v)
        Nothing -> discard


-- | All terms reduce to inert versions (NB:well-typed terms only)
prop_reduce_exists_inert :: forall n. SNatI n => Tm n -> Property
prop_reduce_exists_inert t =
    within 1000000 $
    case reduce t of
        Just v -> property (isInert v)
        Nothing -> property False

-- | reduce agrees with eval on closed terms
prop_eval_reduce :: Tm Z -> Property
prop_eval_reduce t =
    discardAfter 1000000 $
    counterexample ("term: " ++ pp t) $
    case eval t of
        Just v -> counterexample ("evals t: " ++ pp v) $
            case reduce t of
            Just i -> counterexample ("reduces to: " ++ pp i) $
                      property (v == i)
            Nothing -> property False
        Nothing -> discard



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
  | Just br <- findBranch e brs = Just br
  | Just e' <- step e            = Just (Match e' brs)
  | otherwise                    = Nothing

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
normalize (Match e brs) = do
    v <- normalize e
    case findBranch v brs of
        Just body -> normalize body
        Nothing   -> do
            brs' <- mapM normBranch brs
            return (Match v brs')
  where
    normBranch :: Branch n -> Maybe (Branch n)
    normBranch (Branch b) = do
            body' <- normalize (Pat.getBody b)
            return (Branch (Pat.bind (Pat.getPat b) body'))

-- | A term is in normal form when it contains no beta redexes anywhere,
-- including inside lambda bodies and match branches.
isNormal :: Tm n -> Bool
isNormal (Var _)                  = True
isNormal (Lam b)                  = isNormal (getBody1 b)
isNormal Unit                     = True
isNormal (Pair e1 e2)             = isNormal e1 && isNormal e2
isNormal (Inj _ e)                = isNormal e
isNormal (App (Lam _) a)          | isVal a  = False   -- CBV beta redex
isNormal (App f a)                = isNormal f && isNormal a
isNormal (Match e brs) = case findBranch e brs of
    Just _  -> False
    Nothing -> isNormal e && all (\(Branch b) -> isNormal (Pat.getBody b)) brs

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
noRedexUnderBinder (Match e brs) = noRedexUnderBinder e && 
   all (\(Branch b) -> isNormal (Pat.getBody b)) brs


-------------------------------------------------------------------
-- Run all properties
-------------------------------------------------------------------

testAll :: IO ()
testAll = do
    let args = stdArgs { maxSuccess = 1000 }
    putStrLn "prop_evalVal:"                
    quickCheckWith args (forAll0 Scoped PureLC prop_evalVal)
    putStrLn "prop_eval_exists_Val:"      
    quickCheckWith args (forAll0 Typed Full prop_eval_exists_Val)
    putStrLn "prop_reduce_inert @Z:"       
    quickCheckWith args (forAll0 Scoped Full (prop_reduce_inert @Z))
    putStrLn "prop_reduce_inert @(S Z):"   
    quickCheckWith args (forAll1 Scoped Full (prop_reduce_inert @(S Z)))
    putStrLn "prop_reduce_inert @Z:"       
    quickCheckWith args (forAll0 Typed Full (prop_reduce_exists_inert @Z))
    putStrLn "prop_reduce_inert @(S Z):"   
    quickCheckWith args (forAll1 Typed Full (prop_reduce_exists_inert @(S Z)))
    putStrLn "prop_eval_reduce:"           
    quickCheckWith args (forAll0 Scoped Full prop_eval_reduce)
    putStrLn "prop_stepVal:"               
    quickCheckWith args (forAll0 Typed Full prop_stepVal)
    putStrLn "prop_evalStep:"             
    quickCheckWith args (forAll0 Typed Full prop_evalStep)
    putStrLn "prop_reduceStep:"            
    quickCheckWith args (forAll1 Scoped Full prop_reduceStep)

    putStrLn "normalize/normal closed"     
    quickCheckWith args (forAll0 Scoped Full (prop_normalize_normal  @Z))
    putStrLn "normalize/normal open"       
    quickCheckWith args (forAll1 Scoped Full (prop_normalize_normal  @(S Z)))
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