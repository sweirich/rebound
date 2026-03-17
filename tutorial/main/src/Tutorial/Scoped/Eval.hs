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

-- | is a term a value?
-- Note: values are closed under substitution by values
isVal :: Tm n -> Bool
isVal (Var x) = True
isVal (Lam b) = True
isVal Unit = True
isVal (Inj i e) = isVal e
isVal (Pair e1 e2) = isVal e1 && isVal e2
isVal e = False


-- make sure that our generator for values only 
-- produces values
prop_genVal :: forall n. SNatI n => Property
prop_genVal = 
    forAll (genFullVal :: Gen (Tm (S n))) $ \ t -> isVal t

-- make sure that values are closed under substitution by values
prop_val_closed :: forall n. SNatI n => Property
prop_val_closed = 
    forAll (genFullVal :: Gen (Tm (S n))) $ \ t -> 
    forAll (genFullVal :: Gen (Tm n))     $ \ u -> 
        isVal (applyE (u .: idE) t)

-- must use a typed generator to avoid infinite loops
-- but if we do so, can observe that all well-typed terms
-- produce values
prop_evalVal :: Property
prop_evalVal = forAll genTypedFull $ \t ->
    counterexample ("term: " ++ pp t) $
    case eval t of
        Just v -> 
            counterexample ("not a value: " ++ pp v) $
            property (isVal v)
        Nothing -> 
            counterexample ("doesn't eval") $
            property False


-- | Evaluating a value is idempotent
prop_evalValIdem :: Property
prop_evalValIdem = forAll genFullVal $ \v ->
    counterexample ("value: " ++ pp v) $
    case eval v of
       Nothing -> discard
       Just v' -> 
          counterexample ("new value: " ++ pp v') $
          v == v'


-- | an inert term is open but cannot reduce any further
-- using weak CBV reduction (may be stuck)
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

-- | weak CBV reduction: produces an *inert* result
reduce :: Tm n -> Maybe (Tm n)
reduce (Var x)      = return (Var x)
reduce (Lam m)      = return (Lam m)
reduce Unit         = return Unit
reduce (Pair e1 e2) = Pair <$> reduce e1 <*> reduce e2
reduce (Inj i m) = do
    t <- reduce m
    return (Inj i t)
reduce (App m n) = do 
    mv <- reduce m
    nv <- reduce n 
    case mv of 
           Lam n | isVal nv   -> reduce (instantiate1 n nv)
           _     | isInert mv -> return (App mv nv)
           _ -> Nothing
reduce (MatchSum  e0 m m') = do
    v <- reduce e0
    case v of
        (Inj 0 v1) | isVal v1 -> reduce (instantiate1 m v1) 
        (Inj 1 v1) | isVal v1 -> reduce (instantiate1 m' v1)
        _ | isInert v -> return (MatchSum v m m')
        _ -> Nothing
reduce (MatchPair e m) = do 
    v <- reduce e 
    case v of
        Pair v1 v2 | isVal v1 && isVal v2 -> reduce (instantiate2 m v2 v1)
        _ | isInert v -> return (MatchPair v m)
        _ -> Nothing
reduce (MatchUnit e m) = do
    v <- reduce e
    case v of 
        Unit -> reduce m
        _ | isInert v -> return (MatchUnit v m)
        _ -> Nothing


prop_reduce_inert :: forall n. SNatI n => Property
prop_reduce_inert = forAll (genTypedFull :: Gen (Tm n)) $ \t ->
    case reduce t of
        Just v -> property (isInert v)
        Nothing -> discard

-- | A term can fail to step if it is a value or if it is stuck
data Outcome = Value | Stuck | Inert

-- | Small-step evaluation function
step :: Tm n -> Either Outcome (Tm n)
step (Var x) = Left Value
step (Lam b) = Left Value
step (App f a) = case step f of 
    Left Stuck -> Left Stuck
    Left Inert -> Left Inert
    Left Value -> case f of 
        Lam b -> case step a of 
                    Left Value -> Right (instantiate1 b a)
                    Left Stuck -> Left Stuck
                    Left Inert -> Left Inert
                    Right a'   -> Right (App f a')
        _ -> Left Stuck
    Right f' -> Right (App f' a)
step Unit = Left Value
step (MatchUnit u s) = case step u of 
    Left Stuck -> Left Stuck
    Left Inert -> Left Inert
    Left Value -> case u of 
            Unit -> Right s
            _    -> Left Stuck
    Right u' -> Right (MatchUnit u' s)
step (Pair a1 a2) = case step a1 of 
    Left Stuck -> Left Stuck
    Left Inert -> Left Inert
    Left Value -> case step a2 of 
        Left Stuck -> Left Stuck
        Left Inert -> Left Inert
        Left Value -> Left Value
        Right a2' -> Right (Pair a1 a2')
    Right a1' -> Right (Pair a1' a2)
step (MatchPair p b) = case step p of 
    Left Stuck -> Left Stuck
    Left Inert -> Left Inert
    Left Value -> case p of 
        Pair v1 v2 -> Right (instantiate2 b v2 v1)
        _ -> Left Stuck
    Right p' -> Right (MatchPair p' b)
step (Inj i a) = case step a of 
    Left Stuck -> Left Stuck
    Left Inert -> Left Inert
    Left Value -> Left Value
    Right a' -> Right (Inj i a')
step (MatchSum s b1 b2) = case step s of 
    Left Stuck -> Left Stuck
    Left Inert -> Left Inert
    Left Value -> case s of 
        Inj 0 v -> Right (instantiate1 b1 v)
        Inj 1 v -> Right (instantiate1 b2 v)
        _ -> Left Stuck
    Right s' -> Right (MatchSum s' b1 b2)


-- | the step function produces a value for closed terms
prop_stepVal :: Property
prop_stepVal = forAll (genTypedFull :: Gen (Tm Z)) $ 
    let loop e = 
          if isVal e then property True
          else case step e of 
             Left _ ->
                counterexample ("stuck at: " ++ pp e) $ 
                property False
             Right e' -> loop e'
    in loop

-- | The step function respects evaluation
prop_evalStep :: Property
prop_evalStep = forAll (genTypedFull :: Gen (Tm Z)) $ \ e ->
    counterexample ("e  = " ++ pp e) $
    within 1000000 $
    case step e of
        Left _   -> property (isVal e)
        Right e' -> counterexample ("e  = " ++ pp e) $
                    counterexample ("e' = " ++ pp e') $
                    eval e == eval e'

