{-|
Module      : Tutorial.Scoped.Eval
Description : Evaluation for the scoped lambda calculus
-}

module Tutorial.Scoped.Eval where

import Tutorial.Scoped.Syntax
import Tutorial.Scoped.Gen
import Test.QuickCheck
import Tutorial.Scoped.ScopeCheck

-------------------------------------------------------------------
-- Evaluator
-------------------------------------------------------------------

-- | (big-step) evaluation function
-- returns nothing in the case of a runtime type error
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
-- Pattern matching (closed terms)
-------------------------------------------------------------------

-- | Compare a pattern against a value, returning an environment binding
-- the pattern variables (if the pattern matches)
patternMatch :: Pat m -> Tm Z -> Maybe(Env Tm m Z)
patternMatch (PVar _) v | isVal v = return (oneE v)
patternMatch PUnit Unit  = return zeroE
patternMatch (PPair p1 p2) (Pair v1 v2) = do
    env1 <- patternMatch p1 v1
    env2 <- patternMatch p2 v2   
    -- appending Envs requires knowing the length of the first
    withSNat (size p2) $ return (env2 .++ env1)
patternMatch (PInj i p) (Inj j v) | i == j = patternMatch p v
patternMatch _ _ = Nothing

-- | Find the first branch whose pattern matches the scrutinee and
-- instantiate its body.
findBranch :: Tm Z -> [Branch Z] -> Maybe (Tm Z)
findBranch _ [] = Nothing
findBranch e (Branch b : rest) =
    case patternMatch (getPat b) e of
        Just r  -> return (instantiate b r)
        Nothing -> findBranch e rest


-- | determine whether a term is a value?
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
    discardAfter 10000 $
    case eval t of
        Just v ->
            counterexample ("not a value: " ++ pp v) $
            property (isVal v)
        Nothing ->
            discard

-- evaluating twice returns the same result
prop_eval_idempotent :: Tm Z -> Property
prop_eval_idempotent = \t ->
    discardAfter 10000 $
    case eval t of
        Just v ->
            counterexample ("v: " ++ pp v) $
            property (eval v == Just v)
        Nothing ->
            discard

-- all terms produce values (NB: this holds for well-typed terms only!)
prop_eval_exists_Val :: Tm Z -> Property
prop_eval_exists_Val = \t ->
    discardAfter 10000 $   -- try changing this to within
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
-- does not reduce under lambda terms
-- returns 'Nothing' for a type error

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
           Lam n | isInert nv -> return (App mv nv)
           _     | isHead mv  -> Nothing
           _     | isInert mv -> return (App mv nv)
           _                  -> Nothing
reduce (Match e brs) = do
    v <- reduce e
    case findBranch' v brs of
        Right br                -> reduce br
        Left Stuck              -> return (Match v brs)
        Left NoMatch            -> Nothing

-------------------------------------------------------------------
-- Pattern matching (open terms)
-------------------------------------------------------------------

-- | When pattern matching open terms, we need to distinguish between 
-- the two ways we may fail to make progress. Either the patter definitely
-- does not match the branch `NoMatch`, or we we are matching against an inert term 
-- and cannot make further progress until it is a value `Stuck`
data Outcome = Stuck | NoMatch deriving (Show, Eq)

-- | Compare a pattern against a value, returning an environment binding
-- the pattern variables (if the pattern matches)
patternMatch' :: Pat m -> Tm n -> Either Outcome (Env Tm m n)
patternMatch' (PVar _) v | isVal v = return (oneE v)
patternMatch' PUnit Unit  = return zeroE
patternMatch' (PPair p1 p2) (Pair v1 v2) = do
    env1 <- patternMatch' p1 v1
    env2 <- patternMatch' p2 v2   
    -- appending two Environments requires knowing their length 
    withSNat (size p2) $ return (env2 .++ env1)
patternMatch' (PInj i p) (Inj j v) | i == j = patternMatch' p v
patternMatch' p (Var _) = Left Stuck
patternMatch' p v | isVal v = Left NoMatch
patternMatch' _ _ = Left Stuck

-- | Find the first branch whose pattern matches the scrutinee and
-- instantiate its body.
findBranch' :: Tm n -> [Branch n] -> Either Outcome (Tm n)
findBranch' _ [] = Left NoMatch
findBranch' e (Branch b : rest) =
    case patternMatch' (getPat b) e of
        Right r  -> Right (instantiate b r)
        Left NoMatch -> findBranch' e rest
        Left Stuck -> Left Stuck



-- | an inert term is stuck on a variable and cannot 
-- reduce any further
isInert :: Tm n -> Bool
isInert (Var x) = True
isInert (Lam b) = True
isInert Unit    = True
isInert (Pair e1 e2)    = isInert e1 && isInert e2
isInert (Inj i e)       = isInert e
isInert (App (Lam _) u) = isInert u && not (isVal u)
isInert (App t u)       = isInert t && isInert u
isInert (Match e brs)   = isInert e && 
  case findBranch' e brs of
    Right _  -> False
    Left Stuck -> True
    Left NoMatch -> False

isHead :: Tm n -> Bool
isHead (Lam b) = True
isHead Unit    = True
isHead (Pair e1 e2)    = isInert e1 && isInert e2
isHead (Inj i e)       = isInert e
isHead _ = False

-------------------------------------------------------------------
-- Properties of 'reduce'
-------------------------------------------------------------------

-- | reduce agrees with eval on closed terms
prop_eval_reduce :: Tm Z -> Property
prop_eval_reduce t =
    discardAfter 1000000 $
    case eval t of
        Just v -> counterexample ("evals t: " ++ pp v) $
            case reduce t of
            Just i -> counterexample ("reduces to: " ++ pp i) $
                      property (v == i)
            Nothing -> property False
        Nothing -> 
            case reduce t of 
                Just i -> counterexample ("reduces to: " ++ pp i) $ property False
                Nothing -> property True


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
    discardAfter 1000000 $
    case reduce t of
        Just v ->  property (isInert v)
        Nothing -> property False

prop_reduce_exists_inert1 :: Tm N1 -> Property
prop_reduce_exists_inert1 t =
    let pp' = ppWith ("x" ::: VNil) in
    discardAfter 1000000 $
    case reduce t of
        Just v -> counterexample ("reduces to: " ++ pp' v) $ property (isInert v)
        Nothing -> property False

-------------------------------------------------------------------
-- Run all properties
-------------------------------------------------------------------

testAll :: IO ()
testAll = do
    let args = stdArgs { maxSuccess = 10000 }
    putStrLn "prop_evalVal:"                
    quickCheckWith args (forAll0 Scoped PureLC prop_evalVal)
    putStrLn "prop_eval_idempotent:"                
    quickCheckWith args (forAll0 Scoped PureLC prop_eval_idempotent)
    putStrLn "prop_eval_exists_Val:"      
    quickCheckWith args (forAll0 Typed Full prop_eval_exists_Val)
    putStrLn "prop_reduce_inert0:"       
    quickCheckWith args (forAll0 Scoped Full (prop_reduce_inert @Z))
    putStrLn "prop_reduce_inert1:"   
    quickCheckWith args (forAll1 Scoped Full (prop_reduce_inert @(S Z)))
    putStrLn "prop_reduce_exists_inert0:"       
    quickCheckWith args (forAll0 Typed Full (prop_reduce_exists_inert @Z))
    putStrLn "prop_reduce_exists_inert1:"   
    quickCheckWith args (forAll1 Typed Full (prop_reduce_exists_inert @(S Z)))
    putStrLn "prop_eval_reduce:"           
    quickCheckWith args (forAll0 Scoped Full prop_eval_reduce)
    