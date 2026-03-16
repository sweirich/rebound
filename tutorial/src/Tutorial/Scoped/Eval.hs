{-|
Module      : Tutorial.Scoped.Eval
Description : Big-step and small-step evaluators for the scoped lambda calculus

Both evaluators operate on closed terms ('Tm' 'Z').  
The big-step 'eval' returns a value or Nothing on an error;
the small-step 'step' returns 'Left' 'Value' when the term is already a
value, 'Left' 'Stuck' when evaluation is blocked, or 'Right' @e'@ for the
next term.
-}

module Tutorial.Scoped.Eval where

import Tutorial.Scoped.Syntax
import Tutorial.Scoped.Gen
import Test.QuickCheck

-- | (big-step) evaluation function 
eval :: Tm n -> Maybe (Tm n)
eval (Var x)      = return (Var x)
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
           _ | isNeutral mv -> return (App mv nv)
           _ -> Nothing
eval (MatchSum  e0 m m') = do
    v <- eval e0
    case v of
        (Inj 0 v1) -> eval (instantiate1 m v1) 
        (Inj 1 v1) -> eval (instantiate1 m' v1)
        _ | isNeutral v -> return (MatchSum v m m')
        _ -> Nothing
eval (MatchPair e m) = do 
    v <- eval e 
    case v of
        Pair v1 v2 | isVal v1 && isVal v2 -> eval (instantiate2 m v2 v1)
        _ | isNeutral v -> return (MatchPair v m)
        _ -> Nothing
eval (MatchUnit e m) = do
    v <- eval e
    case v of 
        Unit -> eval m
        _ | isNeutral v -> return (MatchUnit v m)
        _ -> Nothing

-- | is a term a value?
isVal :: Tm n -> Bool
isVal (Var x) = True
isVal (Lam b) = True
isVal Unit = True
isVal (Inj i e) = isVal e
isVal (Pair e1 e2) = isVal e1 && isVal e2
isVal e = False

isNeutral :: Tm n -> Bool
isNeutral (Var x) = True
isNeutral (App t u) = isNeutral t
isNeutral (MatchUnit t u) = isNeutral t
isNeutral (MatchPair t u) = isNeutral t
isNeutral (MatchSum t u1 u2) = isNeutral t
isNeutral _ = False

-- | A term can fail to step if it is a value or if it is stuck
data Outcome = Value | Stuck | Neutral

-- | Small-step evaluation function
step :: Tm n -> Either Outcome (Tm n)
step (Var x) = Left Value
step (Lam b) = Left Value
step (App f a) = case step f of 
    Left Stuck -> Left Stuck
    Left Neutral -> Left Neutral
    Left Value -> case f of 
        Lam b -> case step a of 
                    Left Value -> Right (instantiate1 b a)
                    Left Stuck -> Left Stuck
                    Left Neutral -> Left Neutral
                    Right a' -> Right (App f a')
        _ -> Left Stuck
    Right f' -> Right (App f' a)
step Unit = Left Value
step (MatchUnit u s) = case step u of 
    Left Stuck -> Left Stuck
    Left Neutral -> Left Neutral
    Left Value -> case u of 
            Unit -> Right s
            _    -> Left Stuck
    Right u' -> Right (MatchUnit u' s)
step (Pair a1 a2) = case step a1 of 
    Left Stuck -> Left Stuck
    Left Neutral -> Left Neutral
    Left Value -> case step a2 of 
        Left Stuck -> Left Stuck
        Left Neutral -> Left Neutral
        Left Value -> Left Value
        Right a2' -> Right (Pair a1 a2')
    Right a1' -> Right (Pair a1' a2)
step (MatchPair p b) = case step p of 
    Left Stuck -> Left Stuck
    Left Neutral -> Left Neutral
    Left Value -> case p of 
        Pair v1 v2 -> Right (instantiate2 b v2 v1)
        _ -> Left Stuck
    Right p' -> Right (MatchPair p' b)
step (Inj i a) = case step a of 
    Left Stuck -> Left Stuck
    Left Neutral -> Left Neutral
    Left Value -> Left Value
    Right a' -> Right (Inj i a')
step (MatchSum s b1 b2) = case step s of 
    Left Stuck -> Left Stuck
    Left Neutral -> Left Neutral
    Left Value -> case s of 
        Inj 0 v -> Right (instantiate1 b1 v)
        Inj 1 v -> Right (instantiate1 b2 v)
        _ -> Left Stuck
    Right s' -> Right (MatchSum s' b1 b2)


