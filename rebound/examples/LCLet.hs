-- |
-- Module      : LC
-- Description : Untyped lambda calculus
-- Stability   : experimental
--
-- An implementation of the untyped lambda calculus including let, letrec,
-- mutual letrec and let* expressions.
-- TODO: add example terms and fix Show instance
module LCLet where

import Rebound
import Rebound.Bind.Single
import qualified Rebound.Bind.Pat as Pat
import Rebound.Bind.PatN as PatN (BindN, bindN, instantiateN, getBodyN)
import Data.Fin
import Data.Vec qualified as Vec

-- | Datatype of well-scoped lambda-calculus expressions
data Exp (n :: Nat) where
  Var :: Fin n -> Exp n
  Lam :: Bind Exp Exp n -> Exp n
  App :: Exp n -> Exp n -> Exp n
  Let ::
    -- | single let expression
    -- "let x = e1 in e2" where x is bound in e2
    Exp n ->
    (Bind Exp Exp n) ->
    Exp n
  LetRec ::
    -- | "let rec x = e1 in e2" where x is bound in both e1 and e2
    Rec n ->
    Exp n
  LetTele ::
    -- | sequence of nested lets, where each one may depend on
    -- the previous binding
    -- "let x1 = e1 in x2 = e2 in ... in e" where x1 is bound
    -- in e2, e3 ... and e, x2 is bound in e3 and e, etc.
    Tele n ->
    Exp n
  LetMutRec ::
    -- | mutual recursive lets, where each one may depend on
    -- any other variable
    -- "let x1 = e1 in x2 = e2 in ... in e" where x1 ... xn
    -- are bound in e1, e2, e3 ... and e
    MutRec n ->
    Exp n

data Rec n =
  Rec { rec_rhs  :: Bind Exp Exp n,   -- single RHS
        rec_body :: Bind Exp Exp n }  -- body of let

data MutRec n = forall m. SNatI m =>
  MutRec { mutrec_rhss :: Vec m (BindN Exp Exp m n), -- Vector of RHSs
           mutrec_body :: BindN Exp Exp m n  -- body of let
           }

data Tele n where
  LetStar :: Exp n -> Bind Exp Tele n -> Tele n
  Body :: Exp n -> Tele n

----------------------------------------------
-- Example lambda-calculus expressions
----------------------------------------------

-- some variables
v0 :: Exp (S n)
v0 = Var f0
v1 :: Exp (S (S n))
v1 = Var f1
v2 :: Exp (S (S (S n)))
v2 = Var f2
-- | an application expression
(@@) :: Exp n -> Exp n -> Exp n
(@@) = App
-- | a lambda expression
lam :: Exp (S n) -> Exp n
lam = Lam . bind

letrec :: Exp (S n) -> Exp (S n) -> Exp n
letrec e1 e2 = LetRec (Rec (bind e1) (bind e2))

letstar :: Exp n -> Tele (S n) -> Tele n
letstar e t = LetStar e (bind t)

-- | The identity function "λ x. x".
-- With de Bruijn indices we write it as "λ. 0"
-- The `bind` function creates the binder
-- t0 :: Exp Z
t0 = lam v0

-- >>> t0
-- (λ. 0)

-- | A larger term "λ x. λy. x ((λ z. z) y)"
-- λ. λ. 1 ((λ. 0) 0))
t1 :: Exp Z
t1 = lam (lam (v1 @@ ((lam v0) @@ v0)))

-- >>> t1
-- (λ. (λ. (1 ((λ. 0) 0))))

-- let x = \y.y in x x
t2 :: Exp Z
t2 = Let t0 (bind (App v0 v0))

-- >>> t2
-- (let (λ. 0) in (0 0))

-- let rec fix = \f. f (fix f) in f
t3 :: Exp Z
t3 = letrec (lam (v0 @@(v1 @@ v0))) v0
-- >>> t3
-- (let rec (λ. (0 (1 0))) in 0)

-- let* x1 = \x.x ; x2 = x1 x1 ; x3 = x2 s1 in x3 x2 x1
t4 = LetTele
       (letstar t0
         (letstar (v0 @@ v0)
            (letstar (v0 @@ v1)
              (Body ((v0 @@ v1) @@ v2)))))

-- >>> t4
-- <let-tele>

----------------------------------------------
-- (Alpha-)Equivalence
----------------------------------------------

-- | The derivable equality instance
-- is alpha-equivalence
deriving instance (Eq (Exp n))

deriving instance (Eq (Tele n))

deriving instance (Eq (Rec n))

instance Eq (MutRec n) where
  (==) :: MutRec n -> MutRec n -> Bool
  MutRec { mutrec_rhss= (rhss1 :: Vec m1 t1), mutrec_body=body1} ==
    MutRec { mutrec_rhss= (rhss2 :: Vec m2 t2), mutrec_body=body2}
    = case testEquality (snat @m1) (snat @m2) of
       Just Refl -> Vec.all2 (==) rhss1 rhss2 && body1 == body2
       Nothing -> False
----------------------------------------------
-- Substitution
----------------------------------------------

-- To work with this library, we need two type class instances.

-- | Tell the library how to construct variables in the expression
-- type. This class is necessary to construct an indentity
-- substitution---one that maps each variable to itself.
instance SubstVar Exp where
  var :: Fin n -> Exp n
  var = Var

-- The library represents a substitution using an "Environment".
-- The type `Env Exp n m` is a substitution that can be applied to
-- indices bounded by n. It produces a result `Exp` with indices
-- bounded by m. The function `applyEnv` looks up a mapping in
-- an environment.

-- | The operation `applyE` applies an environment
-- (explicit substitution) to an expression.
--
-- The implementation of this operation applies the environment to
-- variable index in the variable case. All other caseas follow
-- via recursion. The library includes a type class instance for
-- the Bind type which handles the variable lifting needed under
-- the binder.
instance Shiftable Exp where
  shift = shiftFromApplyE @Exp
instance Subst Exp Exp where
  applyE :: Env Exp n m -> Exp n -> Exp m
  applyE r (Var x) = applyEnv r x
  applyE r (Lam b) = Lam (applyE r b)
  applyE r (App e1 e2) = App (applyE r e1) (applyE r e2)
  applyE r (Let e1 e2) = Let (applyE r e1) (applyE r e2)
  applyE r (LetRec e) = LetRec (applyE r e)
  applyE r (LetTele e) = LetTele (applyE r e)
  applyE r (LetMutRec e) = LetMutRec (applyE r e)

instance Subst Exp Rec where
  applyE r (Rec rhs body) = Rec (applyE r rhs) (applyE r body)

instance Shiftable Tele where
  shift = shiftFromApplyE @Exp
instance Subst Exp Tele where
  applyE r (Body e) = Body (applyE r e)
  applyE r (LetStar e1 e2) = LetStar (applyE r e1) (applyE r e2)

instance Subst Exp MutRec where
  applyE r (MutRec rhss body) =
    MutRec (fmap (applyE r) rhss) (applyE r body)

----------------------------------------------
-- Display (Show)
----------------------------------------------

-- | To show lambda terms, we use a simple recursive instance of
-- Haskell's `Show` type class. In the case of a binder, we use the `getBody`
-- operation to access the body of the lambda expression.
instance Show (Exp n) where
  showsPrec :: Int -> Exp n -> String -> String
  showsPrec _ (Var x) = shows x
  showsPrec d (App e1 e2) =
    showParen True $
      showsPrec 10 e1
        . showString " "
        . showsPrec 11 e2
  showsPrec d (Lam b) =
    showParen True $
      showString "λ. "
        . shows (getBody b)
  showsPrec d (Let e1 e2) =
    showParen True $
      showString "let "
        . showsPrec 10 e1
        . showString " in "
        . shows (getBody e2)
  showsPrec d (LetRec (Rec{rec_rhs=rhs,rec_body=body})) =
    showParen True $
      showString "let rec "
        . shows (getBody rhs)
        . showString " in "
        . shows (getBody body)
  showsPrec d (LetTele e) = showString "<let-tele>"
  showsPrec d (LetMutRec (MutRec {mutrec_rhss=rhss, mutrec_body=body})) =
    showParen True $
      showString "let rec "
        . showString " rhss " -- (getBodyN e1)
        . showString " in "
        . shows (getBodyN body)
-----------------------------------------------
-- (big-step) evaluation
-----------------------------------------------

-- >>> eval t1
-- (λ. (λ. (1 ((λ. 0) 0))))

-- >>> eval (t1 @@ t0)
-- (λ. ((λ. 0) ((λ. 0) 0)))

-- >>> eval t2
-- (λ. 0)

-- This one is an infinite loop
-- >>> eval t3
-- ProgressCancelledException

-- >>> eval t4
-- (λ. 0)

eval :: Exp n -> Exp n
eval (Var x) = Var x
eval (Lam b) = Lam b
eval (App e1 e2) =
  let v = eval e2
   in case eval e1 of
        Lam b -> eval (instantiate b v)
        t -> App t v
eval (Let e1 e2) =
  eval (instantiate e2 (eval e1))
eval (LetRec e) =
  -- use a Haskell recursive definition
  -- to tie the knot for a recursive definition
  -- in the object language
  let v = instantiate (rec_rhs e) v
   in eval (instantiate (rec_body e) v)
eval (LetTele e) = evalTele e
eval (LetMutRec (MutRec { mutrec_rhss = rhss, mutrec_body = body})) =
  -- use a Haskell recursive definition
  let vs = fmap (\b -> instantiateN b vs) rhss
  in eval (instantiateN body vs)

evalTele :: Tele n -> Exp n
evalTele (Body e) = eval e
evalTele (LetStar e t) =
  evalTele (instantiate t (eval e))
