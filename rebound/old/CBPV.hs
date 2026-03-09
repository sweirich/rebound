{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module CBPV where

import Rebound hiding (Ctx)
import Rebound.Bind.PatN hiding (Ctx)

-- Value Types (A)
data ValTy = U CompTy | One |  ValTy :× ValTy | ValTy :+ ValTy | Zero
  deriving (Eq)
-- Computation Types (B)
data CompTy = F ValTy | ValTy :-> CompTy | CompTy :* CompTy  
  deriving (Eq)

-- Values (V, W)
data Val (n :: Nat) where
    Var   :: Fin n -> Val n
    Thunk :: Comp n -> Val n
    Unit  :: Val n
    Pair  :: Val n -> Val n -> Val n
    Inj   :: Int -> Val n -> Val n
    AnnV :: Val n -> ValTy -> Val n 
       deriving (Generic1)

-- Computations (M, N)
data Comp (n :: Nat) where

    -- elimination forms for values
    Force     :: Val n -> Comp n
    MatchUnit :: Val n -> Comp n -> Comp n
    MatchPair :: Val n -> Bind2 Val Comp n -> Comp n
    MatchSum  :: Val n -> Bind1 Val Comp n -> Bind1 Val Comp n -> Comp n

    -- return/"M to x. N"
    Return :: Val n -> Comp n
    Let    :: Comp n -> Bind1 Val Comp n -> Comp n

    -- function
    Lam :: Bind1 Val Comp n -> Comp n
    App :: Comp n -> Val n -> Comp n

    -- tuples
    Pi   :: Comp n -> Comp n -> Comp n
    Prj  :: Int -> Comp n -> Comp n  

    -- error
    Error :: String -> Comp n

    -- type annotation
    AnnC  :: Comp n -> CompTy -> Comp n
      deriving (Generic1)

instance SubstVar Val where
    var = Var
instance Subst Val Val where
  isVar (Var x) = Just (Refl, x)
  isVar _ = Nothing
instance Subst Val Comp

deriving instance Eq (Val n)
deriving instance Eq (Comp n)
 
--------------------------------------------------------------------
--------------------------------------------------------------------
-- Type checker

type Ctx n = Fin n -> ValTy
emptyCtx :: Ctx Z
emptyCtx = \x -> case x of {}
(+%) :: Ctx n -> ValTy -> Ctx (S n)
(+%) g a = \x -> case x of { FZ -> a ; FS y -> g y }

-- Check the type of a value
tcVal :: Ctx n -> Val n -> ValTy -> Either String ()
tcVal g (Thunk m)    (U b) = tcComp g m b
tcVal g (Pair v1 v2) (a1 :× a2) = do 
    tcVal g v1 a1
    tcVal g v2 a2
tcVal g (Inj 0 v1)   (a1 :+ a2) = tcVal g v1 a1
tcVal g (Inj 1 v1)   (a1 :+ a2) = tcVal g v1 a2
-- catch all
tcVal g v a1 = do
    a2 <- tiVal g v
    if a1 == a2 then return () else Left "type error"

-- Infer the type of a value
tiVal :: Ctx n -> Val n -> Either String ValTy
tiVal g (AnnV v a) = do
    tcVal g v a 
    return a
tiVal g (Var x) = return (g x)
tiVal g Unit = return One
tiVal g (Thunk m) = do
    b <- tiComp g m
    return (U b)
tiVal g (Pair v1 v2) = do 
    a1 <- tiVal g v1 
    a2 <- tiVal g v2 
    return (a1 :× a2)
tiVal g _ = Left "annotation needed"

-- Infer the type of a computation
tiComp :: Ctx n -> Comp n -> Either String CompTy
tiComp g (AnnC m b) = do
    tcComp g m b  
    return b
tiComp g (Force v) = do
    a <- tiVal g v
    case a of 
        U b -> return b
        _ -> Left "type error"
tiComp g (MatchUnit v m) = do
    tcVal g v One
    tiComp g m 
tiComp g (MatchPair v m) = do
    a <- tiVal g v
    case a of 
        a1 :× a2 -> tiComp ((g +% a1) +% a2) (getBody2 m) 
        _ -> Left "type error"
tiComp g (MatchSum v m1 m2) = do
    a <- tiVal g v
    case a of 
        a1 :+ a2 -> do 
            b1 <- tiComp (g +% a1) (getBody1 m1)
            b2 <- tiComp (g +% a2) (getBody1 m2)
            if b1 == b2 then return b1 else Left "type error"
tiComp g (Return v) = do
    a <- tiVal g v 
    return (F a)
tiComp g (Let m n) = do
    b <- tiComp g m
    case b of 
        F a -> tiComp (g +% a) (getBody1 n)
        _ -> Left "type error"
tiComp g (Lam m) = 
    Left "annotation needed"
tiComp g (App m v) = do
    c <- tiComp g m 
    case c of
        a :-> b -> do
            tcVal g v a
            return b
        _ -> Left "type error"
tiComp g (Pi m1 m2) = do
    b1 <- tiComp g m1 
    b2 <- tiComp g m2 
    return (b1 :* b2)
tiComp g (Prj i m) = do
    b <- tiComp g m 
    case b of 
      b1 :* b2 -> if i==0 then tcComp g m b1 >> return b1 else tcComp g m b2 >> return b2
      _ -> Left "type error"

-- check the type of a computation
tcComp :: Ctx n -> Comp n -> CompTy -> Either String ()

tcComp g (Force v) b = do 
    tcVal g v (U b)
tcComp g (MatchUnit v m) b = do
    tcVal g v One
    tcComp g m b
tcComp g (MatchPair v m) b = do
    a <- tiVal g v
    case a of 
        (a1 :× a2) -> tcComp ((g +% a1) +% a2) (getBody2 m) b
        _ -> Left "type error"
tcComp g (MatchSum v m1 m2) b = do
    a <- tiVal g v
    case a of 
        (a1 :+ a2) -> do 
            tcComp (g +% a1) (getBody1 m1) b 
            tcComp (g +% a2) (getBody1 m2) b

tcComp g (Return v) (F a) = do 
    tcVal g v a
tcComp g (Let m n) b = do
    c <- tiComp g m 
    case c of
        F a -> 
           tcComp (g +% a) (getBody1 n) b
        _ -> Left "type error"

tcComp g (Lam m) (a :-> b) = 
    tcComp (g +% a) (getBody1 m) b
tcComp g (App m v) b = do
    a <- tiVal g v
    tcComp g m (a :-> b)

tcComp g (Pi m1 m2) (b1 :* b2) = do
    tcComp g m1 b1
    tcComp g m2 b2

-- includes Prj, Ann, 
tcComp g m b2 = do
    b1 <- tiComp g m
    if b1 == b2 then 
       return ()
    else 
       Left "type error"

----------------------------------------------------------------------
----------------------------------------------------------------------
-- interpreter

eval :: Comp Z -> Either String (Comp Z)
eval (Return v) = return (Return v)
eval (Let m n) = do
    t <- eval m 
    case t of 
        Return v -> eval (instantiate1 n v)
eval (Lam m) = return (Lam m)
eval (App m v) = do 
    t <- eval m 
    case t of 
        Lam n -> eval (instantiate1 n v)
eval (Pi m m') = return (Pi m m')
eval (Prj i m) = do
    t <- eval m
    case t of 
        Pi n n' -> if i == 0 then eval n else eval n'
eval (Force (Thunk m)) = eval m
eval (MatchSum  (Inj 0 v) m m') = eval (instantiate1 m v) 
eval (MatchSum  (Inj 1 v) m m') = eval (instantiate1 m' v) 
eval (MatchPair (Pair v1 v2) m) = eval (instantiate2 m v1 v2)
eval (MatchUnit Unit m) = eval m
eval (Error s) = Left s