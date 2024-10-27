-- The untyped lambda calculus
module LC where

import Vec
import Subst

{- 

Here is a simple representation of well-scoped lambda calculus terms. 
The natural number index `n` is the scoping level -- a bound on the number 
of free variables that can appear in the term. If `n` is 0, then the 
term must be closed.

The `Var` constructor of this datatype takes an index that must 
be strictly less than this bound. The type `Fin (S n)` has `n` different
elements.

The `Lam` constructor binds a variable. The library exports the type 
`Bind1` that introduces a binder. The type arguments state that the
binder is for expression variables, inside an expression term, that may 
have `n` free variables.

-}

data Exp (n :: Nat) where
    Var   :: Fin n -> Exp n
    Lam   :: Bind1 Exp Exp n -> Exp n
    App   :: Exp n -> Exp n -> Exp n

----------------------------------------------

{- 
To work with this library, we need only create two type class instances.
First, we have to tell the library how to construct variables in the expression
type. This class is necessary to construct an indentity substitution---one that 
maps each variable to itself.
-}

instance SubstVar Exp where
    var :: Fin n -> Exp n
    var = Var

{- We also need an operation `applyE` that applies an explicit substitution 
   to an expression.  The type `Env Exp n m` is the type of an 
   "environment" or "explicit substitution". This data structure 
   is a substitution with domain `Fin n` to terms of type `Exp m`.

   The implementation of this operation applies the environment to 
   variable index in the variable case. All other caseas follow 
   via recursion.
 -}
instance Subst Exp Exp where
    applyE :: Env Exp n m -> Exp n -> Exp m
    applyE r (Var x) = applyEnv r x
    applyE r (Lam b) = Lam (applyE r b)
    applyE r (App e1 e2) = App (applyE r e1) (applyE r e2)

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

-- To show lambda terms, we can write a simple recursive instance of 
-- Haskell's `Show` type class. In the case of a binder, we use the `unbind` 
-- operation to access the body of the lambda expression.

-- >>> t0
-- λ. 0

-- >>> t1
-- λ. λ. 1 (λ. 0 0)

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

-- To compare binders, we only need to `unbind` them
instance Eq (Exp n) => Eq (Bind1 Exp Exp n) where
        b1 == b2 = unbind b1 == unbind b2

-- With the instance above the derivable equality instance
-- is alpha-equivalence
deriving instance (Eq (Exp n))


--------------------------------------------------------

{- We can write the usual operations for evaluating 
   lambda terms to values -}

-- big-step evaluation



-- >>> eval t1
-- λ. λ. 1 (λ. 0 0)

-- >>> eval (t1 `App` t0)
-- λ. λ. 0 (λ. 0 0)

eval :: Exp n -> Exp n
eval (Var x) = Var x
eval (Lam b) = Lam b
eval (App e1 e2) =
    let v = eval e2 in
    case eval e1 of
        Lam b -> eval (instantiate b v)
        t -> App t v

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

-- weak-head normalization
-- to normalize under a lambda expression, we must first unbind 
-- it and then rebind it when finished
  

-- >>> whnf t1
-- λ. λ. 1 0

-- >>> whnf (t1 `App` t0)
-- λ. λ. 0 0

whnf :: Exp n -> Exp n
whnf (Var x) = Var x
whnf (Lam b) = Lam (bind1 (whnf (unbind b)))
whnf (App e1 e2) =
    case whnf e1 of
        Lam b -> instantiate b (whnf e2)
        t -> App t (whnf e2)


--------------------------------------------------------
-- We can also write functions that manipulate the 
-- environment explicitly

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
whnfEnv :: Env Exp m n -> Exp m -> Exp n
whnfEnv r (Var x) = applyEnv r x
whnfEnv r (Lam b) = Lam (applyWith whnfEnv r b)
whnfEnv r (App e1 e2) =
    let n = whnfEnv r e1 in
    case whnfEnv r e1 of
        Lam b -> instantiateWith whnfEnv b n
        t -> App t (whnfEnv r e2)

----------------------------------------------------------------





