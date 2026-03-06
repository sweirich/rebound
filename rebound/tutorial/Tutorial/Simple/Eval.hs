module Tutorial.Simple.Eval where

import Tutorial.Simple.Syntax

-- | (big-step) evaluation function 
eval :: Tm Z -> Either String (Tm Z)
eval (Var x) = case x of {}
eval (Lam m)   = return (Lam m)
eval Unit      = return Unit
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
eval (Ann e t) = eval e
