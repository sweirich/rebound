-- Pure-type system example
module PTS where

import Lib
import qualified Vec
import AutoEnv

-- In a pure type system, terms and types are combined
-- into the same syntactic class

data Exp (n :: Nat) where
    Star  :: Exp n
    Pi    :: Exp n -> Bind Exp Exp n -> Exp n 
    Var   :: Fin n -> Exp n
    Lam   :: Exp n -> Bind Exp Exp n -> Exp n
    App   :: Exp n -> Exp n -> Exp n
    Sigma :: Exp n -> Bind Exp Exp n -> Exp n
    Pair  :: Exp n -> Exp n -> Exp n -> Exp n
    Split :: Exp n -> Bind2 Exp Exp n -> Exp n


----------------------------------------------

instance SubstVar Exp where
    var :: Fin n -> Exp n
    var = Var

instance Subst Exp Exp where
    applyE :: Env Exp n m -> Exp n -> Exp m
    applyE r Star = Star
    applyE r (Pi a b) = Pi (applyE r a) (applyE r b)
    applyE r (Var x) = applyEnv r x
    applyE r (Lam a b) = Lam (applyE r a) (applyE r b)
    applyE r (App e1 e2) = App (applyE r e1) (applyE r e2)
    applyE r (Sigma a b) = Sigma (applyE r a) (applyE r b)
    applyE r (Pair e1 e2 t1) = Pair (applyE r e1) (applyE r e2) (applyE r t1)
    applyE r (Split e1 e2) = Split (applyE r e1) (applyE r e2)

----------------------------------------------

-- Does a variable appear free in a term?

-- >>> appearsFree FZ (App (Var f0) (Var f1))
-- True

-- >>> appearsFree FZ (App (Var f1) (Var f1))
-- False

appearsFree :: Fin n -> Exp n -> Bool
appearsFree n (Var x) = n == x
appearsFree n Star = False
appearsFree n (Pi a b) = appearsFree n a || appearsFree (FS n) (unbind b)
appearsFree n (Lam a b) = appearsFree n a || appearsFree (FS n) (unbind b)
appearsFree n (App a b) = appearsFree n a || appearsFree n b
appearsFree n (Sigma a b) = appearsFree n a || appearsFree (FS n) (unbind b)
appearsFree n (Pair a b t) = appearsFree n a || appearsFree n b || appearsFree n t
appearsFree n (Split a b) = appearsFree n a || appearsFree (FS (FS n)) (unbind2 b)


-- TODO
strengthen :: SNat m -> Exp (Plus m n) -> Maybe (Exp n)
strengthen = undefined

----------------------------------------------
-- Examples

-- The identity function "λ x. x". With de Bruijn indices
-- we write it as "λ. 0"
t0 :: Exp Z 
t0 = Lam Star (bind (Var f0))

-- A larger term "λ x. λy. x (λ z. z z)"
-- λ. λ. 1 (λ. 0 0)
t1 :: Exp Z
t1 = Lam Star (bind (Lam Star (bind (Var f1 `App` 
    (Lam Star (bind (Var f0)) `App` Var f0)))))

-- To show lambda terms, we can write a simple recursive instance of 
-- Haskell's `Show` type class. In the case of a binder, we use the `unbind` 
-- operation to access the body of the lambda expression.

-- >>> t0
-- λ. 0

-- >>> t1
-- λ. λ. 1 (λ. 0 0)

-- Polymorphic identity function and its type

tyid = Pi Star (bind (Pi (Var f0) (bind (Var f1))))
tmid = Lam Star (bind (Lam (Var f0) (bind (Var f0))))

-- >>> tyid
-- Pi *.(0 -> 1)

-- >>> tmid
-- λ. λ. 0


instance Show (Exp n) where
    showsPrec :: Int -> Exp n -> String -> String
    showsPrec _ Star    = showString "*"
    showsPrec d (Pi a b)
      | appearsFree FZ (unbind b) = 
        showParen (d > 10) $
          showString "Pi " .
          shows a .
          showString ". " .
          shows (unbind b)
      | otherwise = 
        showParen (d > 10) $
          showsPrec 11 a .
          showString " -> " .
          showsPrec 10 (unbind b)
    showsPrec d (Sigma a b)
      | appearsFree FZ (unbind b) = 
        showParen (d > 10) $
          showString "Sigma " .
          shows a .
          showString ". " .
          shows (unbind b)
      | otherwise = 
        showParen (d > 10) $
          showsPrec 11 a .
          showString " * " .
          showsPrec 10 (unbind b)
    showsPrec _ (Var x) = shows (toInt x)
    showsPrec d (App e1 e2) = showParen (d > 0) $
                              showsPrec 10 e1 . 
                              showString " " .
                              showsPrec 11 e2
    showsPrec d (Lam t b) = showParen (d > 10) $ 
                             showString "λ. " .
                             shows (unbind b) 
    showsPrec d (Pair e1 e2 t) = showParen (d > 0) $
                              showsPrec 10 e1 . 
                              showString ", " .
                              showsPrec 11 e2
    showsPrec d (Split t b) = showParen (d > 10) $ 
                              showString "split" .
                              showsPrec 10 t .
                              showString " in " .
                              shows (unbind2 b)


-- To compare binders, we only need to `unbind` them
instance Eq (Exp n) => Eq (Bind Exp Exp n) where
        b1 == b2 = unbind b1 == unbind b2

instance Eq (Exp n) => Eq (Bind2 Exp Exp n) where
        b1 == b2 = unbind2 b1 == unbind2 b2

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
eval (Lam a b) = Lam a b
eval (App e1 e2) =
    let v = eval e2 in
    case eval e1 of
        Lam a b -> eval (instantiate b v)
        t -> App t v
eval Star = Star
eval (Pi a b) = Pi a b
eval (Sigma a b) = Sigma a b
eval (Pair a b t) = Pair a b t
eval (Split a b) = 
    case eval a of
      Pair a1 a2 _ -> 
        eval (instantiate2 b (eval a1) (eval a2))
      t -> Split t b
-- small-step evaluation

-- >>> step (t1 `App` t0)
-- Just (λ. λ. 0 (λ. 0 0))

step :: Exp n -> Maybe (Exp n)
step (Var x) = Nothing
step (Lam a b) = Nothing 
step (App (Lam a b) e2) = Just (instantiate b e2)
step (App e1 e2)
 | Just e1' <- step e1 = Just (App e1' e2)
 | Just e2' <- step e2 = Just (App e1 e2')
 | otherwise = Nothing
step Star = Nothing
step (Pi a b) = Nothing
step (Sigma a b) = Nothing
step (Pair a b _) = Nothing
step (Split (Pair a1 a2 _) b) = Just (instantiate2 b a1 a2)
step (Split a b) 
 | Just a' <- step a = Just (Split a' b)
 | otherwise = Nothing 

eval' :: Exp n -> Exp n
eval' e 
 | Just e' <- step e = eval' e'
 | otherwise = e

-- normalization
-- to normalize under a lambda expression, we must first unbind 
-- it and then rebind it when finished
  

-- >>> nf t1
-- λ. λ. 1 0

-- >>> nf (t1 `App` t0)
-- λ. λ. 0 0

-- reduce the term everywhere, as much as possible
nf :: Exp n -> Exp n
nf (Var x) = Var x
nf (Lam a b) = Lam a (bind (nf (unbind b)))
nf (App e1 e2) =
    case nf e1 of
        Lam a b -> nf (instantiate b e2)
        t -> App t (nf e2)
nf Star = Star
nf (Pi a b) = Pi (nf a) (bind (nf (unbind b)))
nf (Sigma a b) = Sigma (nf a) (bind (nf (unbind b)))
nf (Pair a b t) = Pair (nf a) (nf b) (nf t)
nf (Split a b) = 
    case nf a of 
        Pair a1 a2 _ -> nf (instantiate2 b a1 a2)
        t -> Split t (bind2 (nf (unbind2 b)))


-- first find the head form, then normalize
whnf :: Exp n -> Exp n
whnf (App a1 a2) = case whnf a1 of 
                    Lam a b -> whnf (instantiate b a1)
                    t -> App t (norm a2)
whnf (Split a b) = case whnf a of 
                    Pair a1 a2 _ -> whnf (instantiate2 b a1 a2)
                    t -> Split a (bind2 (norm (unbind2 b)))
whnf a = a

norm :: Exp n -> Exp n
norm a = case whnf a of 
           Lam a b -> Lam (norm a) (bind (norm (unbind b)))
           Pi a b -> Pi (norm a) (bind (norm (unbind b)))
           Sigma a b -> Sigma (norm a) (bind (norm (unbind b)))
           Pair a b t -> Pair (norm a) (norm b) (norm t)
           Star -> Star
           App a b -> App a b
           Split a b -> Split a b 
           Var x -> Var x

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
evalEnv r (Lam a b) = applyE r (Lam a b)
evalEnv r (App e1 e2) =
    let v = evalEnv r e2 in
    case evalEnv r e1 of
        Lam a b -> 
            unbindWith (\r' e' -> evalEnv (v .: r') e') b
        t -> App t v
evalEnv r Star = Star
evalEnv r (Pi a b) = applyE r (Pi a b)
evalEnv r (Sigma a b) = applyE r (Sigma a b)
evalEnv r (Pair a b t) = applyE r (Pair a b t)
evalEnv r (Split a b) = 
    case evalEnv r a of 
        Pair a1 a2 _ -> 
            unbind2With (\r' e' -> 
                evalEnv (a1 .: (a2 .: (r' .>> r))) e') b
        t -> Split t (applyE r b)

----------------------------------------------------------------


-- TODO: add conversion

typeCheck :: forall n. Ctx Exp n -> Exp n -> Maybe (Exp n)
typeCheck g (Var x) = Just (applyEnv g x)
typeCheck g Star = Just Star
typeCheck g (Pi a b) = do
    tyA <- typeCheck g a
    tyB <- typeCheck (g +++ a) (unbind b)
    if tyA == Star && tyB == Star then return Star else Nothing
typeCheck g (Lam a b) = do
    tyA <- typeCheck g a 
    tyB <- typeCheck (g +++ a) (unbind b)
    if tyA == Star then return $ Pi a (bind tyB) else Nothing
typeCheck g (App a b) = do
    tyA <- typeCheck g a
    tyB <- typeCheck g b
    case tyA of 
        Pi tyA1 tyB1 -> if tyB == tyA1 then return $ instantiate tyB1 b else Nothing
        _ -> Nothing 
typeCheck g (Sigma a b) = do
    tyA <- typeCheck g a
    tyB <- typeCheck (g +++ a) (unbind b)
    if tyA == Star && tyB == Star then return Star else Nothing
typeCheck g (Pair a b ty) = do 
    tyA <- typeCheck g a 
    tyB <- typeCheck g b 
    case ty of 
        (Sigma tyA' tyB') -> 
            if tyA == tyA' && tyB == instantiate tyB' a 
            then Just ty
            else Nothing
        _ -> Nothing
    Nothing
typeCheck g (Split a b) = do
    tyA <- typeCheck g a 
    case tyA of 
        Sigma tyA' tyB -> do
            let g' :: Ctx Exp (S (S n))
                g' = g +++ tyA' +++ unbind tyB
            tyB <- typeCheck g' (unbind2 b) 
            strengthen s2 tyB
        _ -> Nothing


emptyE :: Ctx Exp Z 
emptyE = Env $ \case

-- >>> typeCheck emptyE tmid
-- Just (Pi *. 0 -> 1)

-- >>> typeCheck emptyE (App tmid tyid)
-- Just ((Pi *. 0 -> 1) -> Pi *. 0 -> 1)
