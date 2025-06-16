module LinLC where

import Control.Monad
import Control.Monad.Except
import Data.Fin
import Data.Vec hiding (bind)
import Rebound hiding (rescope, tail, tabulate)
import Rebound.Bind.Single hiding (rescope)
import Rebound.MonadScoped
import Prelude hiding (tail)

--------------------------------------------------------------------------------
--- Basic definitions
--------------------------------------------------------------------------------

-- See LC.hs for more explanations about (very similar) definitions

data Usage where
  Unused :: Usage
  Used :: Usage
  deriving (Show, Eq)

data Ty where
  TyUnit :: Ty
  TyArrow :: Ty -> Ty -> Ty
  deriving (Show, Eq)

data Exp (n :: Nat) where
  Var :: Fin n -> Exp n
  CUnit :: Exp n
  Lam :: Bind Exp Exp n -> Exp n
  App :: Exp n -> Exp n -> Exp n
  deriving (Eq, Generic1)

instance (Eq (Exp n)) => Eq (Bind Exp Exp n) where
  l == r = getBody l == getBody r

instance SubstVar Exp where var = Var

instance Subst Exp Exp where
  isVar (Var x) = Just (Refl, x)
  isVar _ = Nothing

eval :: Exp Z -> Exp Z
eval (Var x) = case x of {}
eval CUnit = CUnit
eval (Lam b) = Lam b
eval (App e1 e2) =
  let v = eval e2
   in case eval e1 of
        Lam b -> eval (instantiate b v)
        t -> App t v

instance Show (Exp n) where
  showsPrec :: Int -> Exp n -> String -> String
  showsPrec _ (Var x) = shows x
  showsPrec _ CUnit = showString "()"
  showsPrec d (App e1 e2) =
    showParen True $
      showsPrec 10 e1
        . showString " "
        . showsPrec 11 e2
  showsPrec d (Lam b) =
    showParen True $
      showString "λ. "
        . shows (getBody b)

--------------------------------------------------------------------------------
--- Some helper-constructors
--------------------------------------------------------------------------------

-- | a lambda expression
lam :: Exp (S n) -> Exp n
lam = Lam . bind
-- | an application expression
(@@) :: Exp n -> Exp n -> Exp n
(@@) = App
-- | variable with index 0
v0 :: Exp (S n)
v0 = Var f0
-- | variable with index 1
v1 :: Exp (S (S n))
v1 = Var f1
-- | Notation for the arrow type
(~>) :: Ty -> Ty -> Ty
(~>) = TyArrow
infixr 8 ~> 

--------------------------------------------------------------------------------
---
--------------------------------------------------------------------------------

data TCEnv n = TCEnv
  { types :: Vec n Ty,
    usages :: Vec n Usage
  }

type TC n a = ScopedStateT TCEnv (Except String) n a

consumeVar :: Fin n -> TC n Ty
consumeVar i = setUsage i >> getsS ((! i) . types)
  where
    setUsage :: Fin n -> TC n ()
    setUsage i = do
      current <- getsS usages
      let (new, old) = set i Used current
      unless (old == Unused) $ throwError "Variable has already been used."
      modifyS $ \s -> s {usages = new}

    set :: Fin n -> t -> Vec n t -> (Vec n t, t)
    set FZ v (h ::: t) = (v ::: t, h)
    set (FS i) v (h ::: t) =
      let (t', v') = set i v t
       in (h ::: t', v')

addBinder :: Ty -> TC (S n) a -> TC n a
addBinder ty m = rescope up down (do v <- m; checkUsed FZ; return v)
  where
    checkUsed :: Fin n -> TC n ()
    checkUsed i = do
      u <- getsS ((! i) . usages)
      unless (u == Used) $ throwError "Variable was not used."

    up :: TCEnv n -> TCEnv (S n)
    up e = e {types = ty ::: types e, usages = Unused ::: usages e}

    down :: TCEnv (S n) -> TCEnv n
    down e = e {types = tail $ types e, usages = tail $ usages e}

inferType :: Exp n -> TC n Ty
inferType (Var i) = consumeVar i
inferType CUnit = return TyUnit
inferType _ = throwError "Cannot infer type of this construct."

checkType :: Exp n -> Ty -> TC n ()
checkType (Lam bnd) ty = do
  let t = unbindl bnd
  (xTy, tTy) <- ensureArrow ty
  addBinder xTy $ checkType t tTy
  where
    ensureArrow :: Ty -> TC n (Ty, Ty)
    ensureArrow (TyArrow l r) = return (l, r)
    ensureArrow _ = throwError "Type is not arrow."
checkType (App f a) rTy = do
  aTy <- inferType a
  checkType f (TyArrow aTy rTy)
checkType t ty = do
  ty' <- inferType t
  unless (ty == ty') $ throwError "Inferred type does not match expected type."

runTC :: (SNatI n) => Vec n Ty -> TC n a -> Either String a
runTC ts m = runExcept $ evalScopedStateT m initEnv 
  where
    initEnv = TCEnv {types = ts, usages = tabulate $ const Unused}

-- >>> runTC empty $ checkType (lam $ v0) (TyUnit ~> TyUnit)
-- Right ()

-- >>> runTC empty $ checkType (lam $ lam $ v0 @@ v1) (TyUnit ~> (TyUnit ~> TyUnit) ~> TyUnit)
-- Right ()

-- >>> runTC empty $ checkType (lam $ lam $ v1) (TyUnit ~> (TyUnit ~> TyUnit) ~> TyUnit)
-- Left "Variable was not used."

-- >>> runTC empty $ checkType (lam $ lam $ v0) (TyUnit ~> (TyUnit ~> TyUnit) ~> TyUnit)
-- Left "Inferred type does not match expected type."

-- >>> runTC empty $ checkType (lam $ lam $ v0) (TyUnit ~> (TyUnit ~> TyUnit) ~> TyUnit ~> TyUnit)
-- Left "Variable was not used."
