-- | The untyped lambda calculus with pattern matching
-- This example extends the lambda calculus with constants (like 'nil 'cons)
-- and arbitrary pattern matching 
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

-- A branch in a case expression is a pattern binding, i.e. a data structure
-- that binds m variables in some expression body
data Branch (n :: Nat) where
    Branch :: PatBind Exp Exp (Pat m) n -> Branch n

-- The index in the pattern is the number of occurrences of 
-- PVar, i.e. the number variables bound by the pattern. 
-- These variables are ordered left to right.
data Pat (n :: Nat) where
    PVar :: Pat N1  -- binds exactly one
    PApp :: Pat n1 -> Pat n2 -> Pat (Plus n1 n2)
    PCon :: String -> Pat N0

----------------------------------------------
-- The `Pat` type tells us how many variables are bound 
-- the pattern. We can also recover that number 
-- from the pattern itself.

instance Sized (Pat n) where
    type Size (Pat n) = n

    size :: Pat n -> SNat (Size (Pat n))
    size PVar = s1
    size (PApp p1 p2) = sPlus (size p1) (size p2)
    size (PCon s) = s0

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
-- Example terms

-- The identity function "λ x. x". With de Bruijn indices
-- we write it as "λ. 0"
t0 :: Exp Z 
t0 = Lam (bind1 (Var f0))

-- A larger term "λ x. λy. x (λ z. z z)"
-- λ. λ. 1 (λ. 0 0)
t1 :: Exp Z
t1 = Lam (bind1 (Lam (bind1 (Var f1 `App` 
    (Lam (bind1 (Var f0)) `App` Var f0)))))

-- "head function"
-- \x -> case x of [nil -> x ; cons y z -> y]
t2 :: Exp Z
t2 = Lam (bind1 (Case (Var f0) 
      [Branch (patBind @(Pat N0) 
               (PCon "Nil") (Var f0)), 
                Branch (patBind @(Pat N2) 
                  (PCon "Cons" `PApp` PVar `PApp` PVar) (Var f0))]))


--------------------------------------------------------------
-- * Show implementation
--------------------------------------------------------------


-- >>> t0
-- λ. 0

-- >>> t1
-- λ. λ. 1 (λ. 0 0)

-- >>> t2
-- λ. case 0 of [Nil => 0,(Cons 0) 1 => 0]

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
    showsPrec d PVar = showString "V"
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
            

--------------------------------------------------------------
-- * Eq implementation
--------------------------------------------------------------

instance Eq (Pat n) where
    (==) :: Pat n -> Pat n -> Bool
    p1 == p2 = Maybe.isJust (testEquality p1 p2)

-- a general form of equality that does not require the 
-- indices to match
instance TestEquality Pat where
    testEquality :: Pat a -> Pat b -> Maybe (a :~: b)
    testEquality PVar PVar = Just Refl
    testEquality (PApp p1 p2) (PApp p1' p2') = do 
        Refl <- testEquality p1 p1'
        Refl <- testEquality p2 p2'
        return Refl
    testEquality (PCon s1) (PCon s2) | s1 == s2 = Just Refl
    testEquality _ _ = Nothing

instance Eq (Branch n) where
    (==) :: Branch n -> Branch n -> Bool
    (Branch (p1 :: PatBind Exp Exp (Pat m1) n)) ==
      (Branch (p2 :: PatBind Exp Exp (Pat m2) n)) =  
        case testEquality (size (getPat p1) :: SNat m1) 
                          (size (getPat p2) :: SNat m2) of
            Just Refl -> p1 == p2
            Nothing -> False
       
-- To compare simple binders, we need to `unbind` them
instance Eq (Exp n) => Eq (Bind1 Exp Exp n) where
        b1 == b2 = unbind b1 == unbind b2

-- To compare pattern binders, we need to unbind, but also 
-- make sure that the patterns are equal
instance (Sized p, Eq p, Eq (Exp n)) => Eq (PatBind Exp Exp p n) where
        b1 == b2 =
            getPat b1 == getPat b2
             && unPatBind b1 == unPatBind b2

-- With the instance above the derivable equality instance
-- is alpha-equivalence
deriving instance (Eq (Exp n))



--------------------------------------------------------
-- Pattern matching code
--------------------------------------------------------

p1 :: Pat N2
p1 = PApp (PApp (PCon "C") PVar) PVar
p2 :: Pat N3
p2 = PApp (PApp PVar PVar) PVar
e1 :: Exp N0
e1 = App (App (Con "C") (Con "A")) (Con "B")
e2 :: Exp N0
e2 = App (App (Con "D") (Con "A")) (Con "B")

-- >>> patternMatch p1 e1
-- Just [a,b]

-- >>> patternMatch p2 e1
-- Just [c,a,b]

-- >>> patternMatch p1 e2
-- Nothing

-- >>> patternMatch p2 e2
-- Just [d,a,b]

-- | Compare a pattern with an expression, potentially 
-- producing a substitution for all of the variables
-- bound in the pattern
patternMatch :: Pat n -> Exp m -> Maybe (Env Exp n m)
patternMatch PVar e = Just $ oneE e
patternMatch (PApp p1 p2) (App e1 e2)  = do
    env1 <- patternMatch p1 e1
    env2 <- patternMatch p2 e2
    withSNat (size p1) $ return (env1 .++ env2)
patternMatch (PCon s1) (Con s2) = 
    if s1 == s2 then Just zeroE else Nothing
patternMatch _ _ = Nothing


findBranch :: Exp n -> [Branch n] -> Maybe (Exp n)
findBranch e [] = Nothing
findBranch e (Branch bind : brs) = 
    case patternMatch (getPat bind) e of
        Just r -> Just $ instantiatePat bind r
        Nothing -> findBranch e brs

--------------------------------------------------------
-- Eval and step
--------------------------------------------------------


{- We can write the usual operations for evaluating 
   lambda terms to values -}
-- big-step evaluation
-- >>> eval t1
-- λ. λ. 1 (λ. 0 0)
-- >>> eval (t1 `App` t0)
-- λ. λ. 0 (λ. 0 0)
t3 = t2 `App` (((Con "Cons") `App` (Con "1")) `App` (Con "2"))
-- >>> t3
-- λ. case 0 of [Nil => 0,(Cons V) V => 0] ((Cons 1) 2)
-- >>> eval t3
-- 1
eval :: Exp n -> Exp n
eval (Var x) = Var x
eval (Lam b) = Lam b
eval (App e1 e2) =
    let v = eval e2 in
    case eval e1 of
        Lam b -> eval (instantiate b v)
        t -> App t v              -- if cannot reduce, return neutral term
eval (Con s) = Con s
eval (Case e brs) = 
    let v = eval e in
    case findBranch v brs of 
        Just br -> eval br
        Nothing -> Case v brs     -- if cannot reduce, return neutral term

-- | small-step evaluation
-- >>> step (t1 `App` t0)
-- Just (λ. λ. 0 (λ. 0 0))

step :: Exp n -> Maybe (Exp n)
step (Var x) = Nothing
step (Lam b) = Nothing 
step (App (Lam b) e2) = Just (instantiate b e2)
step (App e1 e2)
 | Just e1' <- step e1 = Just (App e1' e2)
 | Just e2' <- step e2 = Just (App e1 e2')
 | otherwise = Nothing
step (Con s) = Nothing
step (Case e brs) 
 | Just br <- findBranch e brs = Just br
 | Just e' <- step e = Just (Case e' brs)
 | otherwise = Nothing
eval' :: Exp n -> Exp n
eval' e 
 | Just e' <- step e = eval' e'
 | otherwise = e

-- full normalization
-- to normalize under a lambda expression, we must first unbind 
-- it and then rebind it when finished
  
-- >>> nf t1
-- λ. λ. 1 0
-- >>> nf (t1 `App` t0)
-- λ. λ. 0 0
nf :: Exp n -> Exp n
nf (Var x) = Var x
nf (Lam b) = Lam (bind1 (nf (unbind b)))
nf (App e1 e2) =
    case nf e1 of
        Lam b -> instantiate b (nf e2)
        t -> App t (nf e2)
nf (Con s) = Con s
nf (Case e brs) = 
    let v = nf e in
    case findBranch v brs of
        Just b -> nf b
        Nothing -> Case e (map nfBr brs)

nfBr :: Branch n -> Branch n
nfBr (Branch bnd) = 
    Branch (patBind (getPat bnd) (nf (unPatBind bnd)))
    
