{-|
Module      : Tutorial.Scoped.SyntaxScratch
Description : Well-scoped abstract syntax for a simply-typed lambda calculus
              with simple pattern matching

-}
module Tutorial.Scoped.SyntaxScratch(
    Ty(..), Tm(..), 
    ex_id, ex_const, ex_comp, ex_swap) where

import Rebound hiding (Ctx)
import Rebound.Bind.PatN 
import Data.Maybe as Maybe
import Data.Fin

--------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------

data Ty = One | Ty :-> Ty | Ty :* Ty | Ty :+ Ty
  deriving (Eq, Show)

data Tm (n :: Nat) where
    Var   :: Fin n -> Tm n
    Lam   :: Bind1 Tm Tm n -> Tm n
    Unit  :: Tm n
    Pair  :: Tm n -> Tm n -> Tm n
    Inj   :: Int -> Tm n -> Tm n
    App   :: Tm n -> Tm n -> Tm n
    -- simple pattern matching
    -- `case e0 of () -> e1`
    MatchUnit :: Tm n -> Tm n -> Tm n
    -- `case e0 of (x,y) -> e1`
    MatchPair :: Tm n -> Bind2 Tm Tm n -> Tm n
    -- `case e0 of {inj1 x -> e1 ; inj2 y -> e2 }`
    MatchSum  :: Tm n -> Bind1 Tm Tm n -> Bind1 Tm Tm n -> Tm n
      deriving (Eq, Show, Generic1)


-- Bind1 and Bind2 are abstract types defined by the library. 

-- >>> :t bind1


-- >>> :t getBody1


-- >>> :t instantiate1


--------------------------------------------------------------------
-- Example terms
--------------------------------------------------------------------

-- | Identity function: λx. x  or  λ.0
ex_id :: Tm Z
ex_id = Lam (bind1 (Var f0))

-- | Constant function: λx. λy. x or λ.λ.1
ex_const :: Tm Z
ex_const = Lam (bind1 (Lam (bind1 (Var f1))))

-- | Function composition: λf. λg. λx. f (g x) or λ.λ.λ. 2 (1 0)
ex_comp :: Tm Z
ex_comp = Lam (bind1 (Lam (bind1 (Lam (bind1
    (App (Var f2) (App (Var f1) (Var f0))))))))

-- | Swap a pair: 
-- λp. case p of (x, y) → (y, x)  
-- λ. case 0 of (,) -> (0,1)
ex_swap :: Tm Z
ex_swap = Lam (bind1 (MatchPair (Var f0) (bind2 (Pair (Var f0) (Var f1)))))


-- >>> ex_id == ex_id

--------------------------------------------------------------------
-- Substitution
--------------------------------------------------------------------

-- Substitution is enabled by 

instance SubstVar Tm where
  var :: Fin n -> Tm n
  var = Var
  
instance Subst Tm Tm where
  isVar :: Tm n -> Maybe (Tm :~: Tm, Fin n)
  isVar (Var x) = Just (Refl, x)
  isVar _ = Nothing


-- >>> applyE (Unit .: zeroE) (Var FZ)
-- Unit



-- >>> applyE (Unit .: zeroE) (Lam (bind1 (Var f1)))
-- Lam (bind1 Unit)

--------------------------------------------------------------------
-- Evaluation function
--------------------------------------------------------------------

-- | (big-step) cbv evaluation function 
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
        Lam b -> eval (instantiate1 b nv)
        _ -> Nothing
eval (MatchSum e0 m m') = do
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


-- Some test cases for the evaluator

-- (\x.\y.x) Unit (Inj0 Unit)
test1 :: Maybe (Tm Z)
test1 = eval (App (App ex_const Unit) (Inj 0 Unit))

--- >>> test1




-- case (Unit, Inj0 Unit) of (x,y) -> y
test2 :: Maybe (Tm Z)
test2 = eval (MatchPair (Pair Unit (Inj 0 Unit)) (bind2 (Var f0)))

-- >>> test2




--------------------------------------------------------------------
-- Show instances for Pat.Bind
--------------------------------------------------------------------

instance (SNatI p) => Show (BindN Tm Tm p n) where
   showsPrec p bnd = 
      showParen (p > 10) $ 
      showString "bind" 
         . showString (show (toInt (snat :: SNat p)))
         . showString " " . showsPrec 11 (getBodyN bnd)
