-- The untyped lambda calculus with pattern matching
-- Evaluation and normalization
module Pat where

import Lib
import qualified Vec
import Subst
import Data.Type.Equality

import qualified Data.Maybe as Maybe

data Exp (n :: Nat) where
    Var   :: Fin n -> Exp n
    Lam   :: Bind1 Exp Exp n -> Exp n
    App   :: Exp n -> Exp n -> Exp n
    Con   :: String -> Exp n
    Case  :: Exp n -> [Branch n] -> Exp n

data Pat (n :: Nat) where
    PVar :: Fin n -> Pat n
    PApp :: Pat n -> Pat n -> Pat n
    PCon :: String -> Pat n

data Branch (n :: Nat) where
    Branch :: SNatI m => PatBind Exp Exp (Pat m) n -> Branch n

----------------------------------------------
-- How many variables are bound in a pattern?

instance SNatI m => Sized (Pat m) where
    type Size (Pat m) = m
    size e = snat

----------------------------------------------

instance SubstVar Exp where
    var :: Fin n -> Exp n
    var = Var

instance Subst Exp Exp where
    applyE :: Env Exp n m -> Exp n -> Exp m
    applyE r (Var x) = applyEnv r x
    applyE r (Lam b) = Lam (applyE r b)
    applyE r (App e1 e2) = App (applyE r e1) (applyE r e2)
    applyE r (Con s) = Con s
    applyE r (Case e brs) = Case (applyE r e) (map (applyE r) brs)

instance Subst Exp Branch where
    applyE :: Env Exp n m -> Branch n -> Branch m
    applyE r (Branch bnd) = Branch (applyE r bnd)

----------------------------------------------
-- Examples

-- The identity function "λ x. x". With de Bruijn indices
-- we write it as "λ. 0"
t0 :: Exp Z 
t0 = Lam (bind1 (Var f0))

-- A larger term "λ x. λy. x (λ z. z z)"
-- λ. λ. 1 (λ. 0 0)
t1 :: Exp Z
t1 = Lam (bind1 (Lam (bind1 (Var f1 `App` 
    (Lam (bind1 (Var f0)) `App` Var f0)))))


t2 :: Exp Z
t2 = Lam (bind1 (Case (Var f0) [Branch (patBind @(Pat N0) 
                                    (PCon "Nil") (Var f0)), 
                                  Branch (patBind @(Pat N2) 
                                    (PCon "Cons" `PApp` PVar f0 `PApp` PVar f1) (Var f0))]))

-- To show lambda terms, we can write a simple recursive instance of 
-- Haskell's `Show` type class. In the case of a binder, we use the `unbind` 
-- operation to access the body of the lambda expression.

-- >>> t0
-- λ. 0

-- >>> t1
-- λ. λ. 1 (λ. 0 0)

-- >>> t2
-- λ. case 0 of[Nil => 0,Cons 0 1 => 0]

instance Show (Exp n) where
    showsPrec :: Int -> Exp n -> String -> String
    showsPrec _ (Var x) = shows (toInt x)
    showsPrec d (App e1 e2) = showParen (d > 0) $
                              showsPrec 10 e1 . 
                              showString " " .
                              showsPrec 11 e2
    showsPrec d (Lam b) = showParen (d > 10) $ 
                          showString "λ. " .
                          shows (unbind b) 
    showsPrec d (Con s) = showString s
    showsPrec d (Case e brs) = showParen (d > 10) $
        showString "case " . 
        shows e .
        showString " of " . 
        shows brs

instance Show (Pat n) where
    showsPrec :: Int -> Pat n -> String -> String
    showsPrec d (PVar x) = shows (toInt x)
    showsPrec d (PApp p1 p2) = showParen (d > 0) $
                              showsPrec 10 p1 . 
                              showString " " .
                              showsPrec 11 p2
    showsPrec d (PCon s) = showString s

instance Show (Branch n) where
    showsPrec :: Int -> Branch n -> String -> String
    showsPrec d (Branch bnd) = 
        shows (getPat bnd) . 
        showString " => " .
        showsPrec d (unPatBind bnd)
            
instance Eq (Branch n) where
    (Branch (p1 :: PatBind Exp Exp (Pat m1) n)) ==
      (Branch (p2 :: PatBind Exp Exp (Pat m2) n)) =  
        case testEquality (snat :: SNat m1) (snat :: SNat m2) of
            Just Refl -> p1 == p2
            Nothing -> False
       
-- To compare binders, we only need to `unbind` them
instance Eq (Exp n) => Eq (Bind1 Exp Exp n) where
        b1 == b2 = unbind b1 == unbind b2

instance (Sized p, Eq (Exp n)) => Eq (PatBind Exp Exp p n) where
        b1 == b2 = unPatBind b1 == unPatBind b2

-- With the instance above the derivable equality instance
-- is alpha-equivalence
deriving instance (Eq (Exp n))
deriving instance (Eq (Pat n))

--------------------------------------------------------
-- this pattern matching code fails if Pat n does not include
-- n different variables 

type PartialEnv n m = Vec n (Maybe (Exp m))

emptyPE :: SNatI n => PartialEnv n m
emptyPE = Vec.repeat snat Nothing

singlePE :: SNatI n => Fin n -> Exp m -> PartialEnv n m
singlePE x e = Vec.setAt x emptyPE (Just e)
                 
mergePE :: PartialEnv n m -> PartialEnv n m -> PartialEnv n m
mergePE = Vec.zipWith $ \m1 m2 -> case (m1,m2) of 
                                 (Just x, _) -> Just x
                                 (_,Just x)  -> Just x
                                 (_,_) -> Nothing

resolvePE :: PartialEnv n m -> Maybe (Env Exp n m)
resolvePE pe = if all Maybe.isJust pe then Just $ Env $ \x -> Maybe.fromJust (pe Vec.! x) else Nothing

patternMatch :: SNatI n => Pat n -> Exp m -> Maybe (PartialEnv n m)
patternMatch (PVar x) e = Just $ singlePE x e
patternMatch (PCon s1) (Con s2) = Just emptyPE
patternMatch (PApp p1 p2) (App e1 e2) = mergePE <$> patternMatch p1 e1 <*> patternMatch p2 e2
patternMatch _ _ = Nothing





