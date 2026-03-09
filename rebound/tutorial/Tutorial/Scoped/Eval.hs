{-|
Module      : Tutorial.Scoped.Eval
Description : Big-step and small-step evaluators for the scoped lambda calculus

Both evaluators operate on closed terms ('Tm' 'Z') to avoid the need for
an environment.  The big-step 'eval' returns a value or an error string;
the small-step 'step' returns 'Left' 'Value' when the term is already a
value, 'Left' 'Stuck' when evaluation is blocked, or 'Right' @e'@ for the
next term.
-}

module Tutorial.Scoped.Eval where

import Tutorial.Scoped.Syntax
import Tutorial.Scoped.Gen
import Test.QuickCheck

-- | (big-step) evaluation function 
eval :: Tm Z -> Either String (Tm Z)
eval (Var x) = case x of {}
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
      _ -> Left "Wrong"
eval (MatchSum  e0 m m') = do
    v <- eval e0
    case v of
        (Inj 0 v1) -> eval (instantiate1 m v1) 
        (Inj 1 v1) -> eval (instantiate1 m' v1)
        _ -> Left "Wrong"
eval (MatchPair e m) = do 
    v <- eval e 
    case v of
        Pair v1 v2 -> eval (instantiate2 m v1 v2)
        _ -> Left "Wrong"
eval (MatchUnit e m) = do
    v <- eval e
    case v of 
        Unit -> eval m
        _ -> Left "Wrong"

-- | is a term a value?
isVal :: Tm Z -> Bool
isVal (Lam b) = True
isVal Unit = True
isVal (Inj i e) = isVal e
isVal (Pair e1 e2) = isVal e1 && isVal e2
isVal e = False


data Outcome = Value | Stuck

-- | Small-step evaluation function
step :: Tm Z -> Either Outcome (Tm Z)
step (Var x) = case x of {}
step (Lam b) = Left Value
step (App f a) = case step f of 
    Left Stuck -> Left Stuck
    Left Value -> case f of 
        Lam b -> case step a of 
                    Left Value -> Right (instantiate1 b a)
                    Left Stuck -> Left Stuck
                    Right a' -> Right (App f a')
        _ -> Left Stuck
    Right f' -> Right (App f' a)
step Unit = Left Value
step (MatchUnit u s) = case step u of 
    Left Stuck -> Left Stuck
    Left Value -> case u of 
            Unit -> Right s
            _    -> Left Stuck
    Right u' -> Right (MatchUnit u' s)
step (Pair a1 a2) = case step a1 of 
    Left Stuck -> Left Stuck
    Left Value -> case step a2 of 
        Left Stuck -> Left Stuck
        Left Value -> Left Value
        Right a2' -> Right (Pair a1 a2')
    Right a1' -> Right (Pair a1' a2)
step (MatchPair p b) = case step p of 
    Left Stuck -> Left Stuck
    Left Value -> case p of 
        Pair v1 v2 -> Right (instantiate2 b v1 v2)
        _ -> Left Stuck
    Right p' -> Right (MatchPair p' b)
step (Inj i a) = case step a of 
    Left Stuck -> Left Stuck
    Left Value -> Left Value
    Right a' -> Right (Inj i a')
step (MatchSum s b1 b2) = case step s of 
    Left Stuck -> Left Stuck
    Left Value -> case s of 
        Inj 0 v -> Right (instantiate1 b1 v)
        Inj 1 v -> Right (instantiate1 b2 v)
        _ -> Left Stuck
    Right s' -> Right (MatchSum s' b1 b2)


