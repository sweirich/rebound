{-|
Module      : Tutorial.Scoped.Eval
Description : Evaluators for the scoped lambda calculus
-}

module Tutorial.Scoped.Eval where

import Tutorial.Scoped.Syntax
import Tutorial.Scoped.Gen
import Test.QuickCheck
import Tutorial.Scoped.ScopeCheck

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
    discardAfter 1000000 $
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
    within 1000000 $
    case eval t of
        Just v -> 
            counterexample ("not a value: " ++ pp v) $
            property (isVal v)
        Nothing -> 
            counterexample ("doesn't eval") $
            property False

-------------------------------------------------------------------
-- CBV reduction for open terms
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
reduce (MatchSum  e0 m m') = do
    v <- reduce e0
    case v of
        (Inj 0 v1) | isVal v1  -> reduce (instantiate1 m v1) 
        (Inj 1 v1) | isVal v1  -> reduce (instantiate1 m' v1)
        _          | isInert v -> return (MatchSum v m m')
        _                      -> Nothing
reduce (MatchPair e m) = do 
    v <- reduce e 
    case v of
        Pair v1 v2 | isVal v   -> reduce (instantiate2 m v2 v1)
        _          | isInert v -> return (MatchPair v m)
        _                      -> Nothing
reduce (MatchUnit e m) = do
    v <- reduce e
    case v of 
        _ | isVal v   -> reduce m
        _ | isInert v -> return (MatchUnit v m)
        _             -> Nothing

-- | an inert term cannot reduce any further
isInert :: Tm n -> Bool
isInert (Var x) = True
isInert (Lam b) = True
isInert (App (Lam _) u) | isVal u  = False
isInert (App t u) = isInert t && isInert u
isInert Unit = True
isInert (MatchUnit Unit _) = False
isInert (MatchUnit t u) = isInert t
isInert (Pair e1 e2) = isInert e1 && isInert e2
isInert (MatchPair t@(Pair _ _) _) | isVal t = False
isInert (MatchPair t u) = isInert t
isInert (Inj i e) = isInert e
isInert (MatchSum t@(Inj _ _) _ _) | isVal t = False
isInert (MatchSum t u1 u2) = isInert t

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
step (MatchUnit u s) 
  | isVal u = Just s
step (MatchUnit u s) = do
    u' <- step u
    return (MatchUnit u' s)
step (Pair a1 a2) | isInert a1 = do
    a2' <- step a2
    return (Pair a1 a2')
step (Pair a1 a2) = do
    a1' <- step a1
    return (Pair a1' a2)
step (MatchPair (Pair v1 v2) b) | isVal v1 && isVal v2 = Just (instantiate2 b v2 v1)
step (MatchPair p b) = do
    p' <- step p
    return (MatchPair p' b)
step (Inj i a) = do
    a' <- step a
    return (Inj i a')
step (MatchSum (Inj 0 v) b1 b2) | isVal v = Just (instantiate1 b1 v)
step (MatchSum (Inj 1 v) b1 b2) | isVal v = Just (instantiate1 b2 v)
step (MatchSum s b1 b2) = do
    s' <- step s
    return (MatchSum s' b1 b2)

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

-------------------------------------------------------------------
-- Run all properties
-------------------------------------------------------------------

testAll :: IO ()
testAll = do
    let args = stdArgs { maxSuccess = 1000 }
    putStrLn "prop_evalVal:"               >> quickCheckWith args (forAll0 Scoped Full prop_evalVal)
    putStrLn "prop_eval_exists_Val:"       >> quickCheckWith args (forAll0 Typed Full prop_eval_exists_Val)

    putStrLn "prop_reduce_inert @Z:"       >> quickCheckWith args (forAll0 Scoped Full (prop_reduce_inert @Z))
    putStrLn "prop_reduce_inert @(S Z):"   >> quickCheckWith args (forAll1 Scoped Full (prop_reduce_inert @(S Z)))

    putStrLn "prop_reduce_inert @Z:"       >> quickCheckWith args (forAll0 Typed Full (prop_reduce_exists_inert @Z))
    putStrLn "prop_reduce_inert @(S Z):"   >> quickCheckWith args (forAll1 Typed Full (prop_reduce_exists_inert @(S Z)))

    putStrLn "prop_eval_reduce:"           >> quickCheckWith args (forAll0 Scoped Full prop_eval_reduce)

    putStrLn "prop_stepVal:"               >> quickCheckWith args (forAll0 Typed Full prop_stepVal)
    putStrLn "prop_evalStep:"              >> quickCheckWith args (forAll0 Typed Full prop_evalStep)
    putStrLn "prop_reduceStep:"            >> quickCheckWith args (forAll1 Scoped Full prop_reduceStep)

