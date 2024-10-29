-- The untyped lambda calculus, with pattern matching
-- Evaluation and normalization
module Pat where

import Vec
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
t0 = Lam (bind1 (Var zero))

-- A larger term "λ x. λy. x (λ z. z z)"
-- λ. λ. 1 (λ. 0 0)
t1 :: Exp Z
t1 = Lam (bind1 (Lam (bind1 (Var one `App` 
    (Lam (bind1 (Var zero)) `App` Var zero)))))


t2 :: Exp Z
t2 = Lam (bind1 (Case (Var zero) [Branch (patBind @(Pat Z) 
                                    (PCon "Nil") (Var zero)), 
                                  Branch (patBind @(Pat Two) 
                                    (PCon "Cons" `PApp` PVar zero `PApp` PVar one) (Var zero))]))

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
-- n different variables. 

type PartialEnv n m = Vec n (Maybe (Exp m))

emptyPE :: SNatI n => PartialEnv n m
emptyPE = vreplicate snat Nothing

singlePE :: SNatI n => Fin n -> Exp m -> PartialEnv n m
singlePE x e = vupdate x emptyPE (Just e)
                 
mergePE :: PartialEnv n m -> PartialEnv n m -> PartialEnv n m
mergePE = vzipWith $ \m1 m2 -> case (m1,m2) of 
                                 (Just x, _) -> Just x
                                 (_,Just x)  -> Just x
                                 (_,_) -> Nothing

resolvePE :: PartialEnv n m -> Maybe (Env Exp n m)
resolvePE pe = if all Maybe.isJust pe then Just $ Env $ \x -> Maybe.fromJust (lookupVec x pe) else Nothing

patternMatch :: SNatI n => Pat n -> Exp m -> Maybe (PartialEnv n m)
patternMatch (PVar x) e = Just $ singlePE x e
patternMatch (PCon s1) (Con s2) = Just emptyPE
patternMatch (PApp p1 p2) (App e1 e2) = mergePE <$> patternMatch p1 e1 <*> patternMatch p2 e2
patternMatch _ _ = Nothing


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
-- λ. case 0 of [Nil => 0,(Cons 0) 1 => 0] ((Cons 1) 2)

-- >>> eval t3
-- 1

eval :: Exp n -> Exp n
eval (Var x) = Var x
eval (Lam b) = Lam b
eval (App e1 e2) =
    let v = eval e2 in
    case eval e1 of
        Lam b -> eval (instantiate b v)
        t -> App t v
eval (Con s) = Con s
eval (Case e brs) = 
    evalBranches (eval e) brs

evalBranches :: Exp n -> [Branch n] -> Exp n
evalBranches e [] = Case e []
evalBranches e (Branch bind : brs) = 
    case patternMatch (getPat bind) e of
        Just pm -> case resolvePE pm of
            Just r -> instantiatePat bind r
            Nothing -> error "not enough binding variables"
        Nothing -> evalBranches e brs

-- small-step evaluation

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


--------------------------------------------------------
-- We can also write functions that manipulate the 
-- environment explicitly. These operations are equivalent
-- to the definitions above, but they provide access to the 
-- suspended substitution during the traversal of the term.

-- >>> evalEnv idE t1
-- λ. λ. 1 (λ. 0 0)

-- Below, if n is 0, then this function acts like an 
-- "environment-based" bigstep evaluator. The result of 
-- evaluating a lambda expression is a closure --- the body 
-- of the lambda paired with its environment. That is exactly 
-- what the implementation of bind does.

-- In the case of beta-reduction, the `unBindWith` operation 
-- applies its argument to the environment and subterm in the
-- closure. In other words, this function calls `evalEnv` 
-- recursively with the saved environment and body of the lambda term.

evalEnv :: Env Exp m n -> Exp m -> Exp n
evalEnv r (Var x) = applyEnv r x
evalEnv r (Lam b) = applyE r (Lam b)
evalEnv r (App e1 e2) =
    let v = evalEnv r e2 in
    case evalEnv r e1 of
        Lam b -> 
            unbindWith (\r' e' -> evalEnv (v .: r') e') b
        t -> App t v

-- To normalize under the binder, the `applyWith` function 
-- takes care of the necessary environment manipulation. It 
-- composes the given environment r with the environment stored
-- in the binder and also shifts them for the recursive call.
--
-- In the beta-reduction case, we could use `unbindWith` as above
-- but the `instantiateWith` function already captures exactly
-- this pattern. 
nfEnv :: Env Exp m n -> Exp m -> Exp n
nfEnv r (Var x) = applyEnv r x
nfEnv r (Lam b) = Lam (applyWith nfEnv r b)
nfEnv r (App e1 e2) =
    let n = nfEnv r e1 in
    case nfEnv r e1 of
        Lam b -> instantiateWith nfEnv b n
        t -> App t (nfEnv r e2)

----------------------------------------------------------------





