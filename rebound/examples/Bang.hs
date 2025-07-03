module Bang where

import Control.Applicative (Alternative ((<|>)))
import LC qualified
import Rebound
import Rebound.Bind.Single
import Data.Fin (f0, f1)
import Control.Monad.Writer (Writer, MonadWriter (..), execWriter)
import Data.List (intersperse)
import Control.Monad (join)

-- From <<The Bang Calculus: an untyped lambda-calculus generalizing
-- Call-By-Name and Call-By-Value>>
-- https://dl.acm.org/doi/abs/10.1145/2967973.2968608

--------------------------------------------------------------------------------
--- Core syntax & handy constructors
--------------------------------------------------------------------------------

data Val n where
  -- x
  Var :: Fin n -> Val n
  -- T!
  Bang :: Tm n -> Val n
  deriving (Generic1)

data Tm n where
  -- V
  Val :: Val n -> Tm n
  -- λx T
  Abs :: Bind Val Tm n -> Tm n
  -- <T>S
  App :: Tm n -> Tm n -> Tm n
  -- der T
  Der :: Tm n -> Tm n
  deriving (Generic1)

-- | a lambda expression
lam :: Tm (S n) -> Tm n
lam = Abs . bind
-- | an application expression
(@@) :: Tm n -> Tm n -> Tm n
(@@) = App
-- | variable with index 0
v0 :: Tm (S n)
v0 = Val $ Var f0
-- | variable with index 1
v1 :: Tm (S (S n))
v1 = Val $ Var f1
-- | Bang
bang :: Tm n -> Tm n
bang t = Val $ Bang t
-- | Dereliction
der :: Tm n -> Tm n
der = Der

--------------------------------------------------------------------------------
--- Pretty printing
--------------------------------------------------------------------------------

instance Show (Val n) where
  showsPrec :: Int -> Val n -> String -> String
  showsPrec _ (Var x) = shows x
  showsPrec _ (Bang t) = showString "!" . shows t

instance Show (Tm n) where
  showsPrec :: Int -> Tm n -> String -> String
  showsPrec _ (Val v) = shows v
  showsPrec _ (App e1 e2) =
      showString "<"
        . shows e1
        . showString "> "
        . shows e2
  showsPrec _ (Abs b) =
      showString "λ. "
        . shows (getBody b)
  showsPrec _ (Der t) = showString "der " . shows t

--------------------------------------------------------------------------------
--- Instances required by rebound
--------------------------------------------------------------------------------

instance SubstVar Val where
  var = Var

instance Subst Val Val where
  isVar (Var x) = Just (Refl, x)
  isVar _ = Nothing

instance Subst Val Tm

--------------------------------------------------------------------------------
--- Reducing & compiling terms
--------------------------------------------------------------------------------

rootStep :: Tm n -> Maybe (Tm n)
-- 'v' reduction
rootStep (App (Abs bnd) (Val v)) = return $ instantiate bnd v
-- '!' reduction
rootStep (Der (Val (Bang t))) = return t
rootStep _ = Nothing

-- Reduction is done in top-down, left-right order
reduce :: Bool -> Tm n -> Maybe (Tm n)
reduce weak t = iter t
  where
    iter, cong :: Tm n -> Maybe (Tm n)
    iter t = rootStep t <|> cong t
    -- Note: we should do that with `applyUnder` for efficiency, but I'm too lazy
    -- for that
    cong (Abs bnd) =
      let b = unbindl bnd
       in Abs . bind <$> iter b
    cong (App l r) =
      case iter l of
        Just l' -> return $ App l' r
        Nothing -> App l <$> iter r
    cong (Der t) = Der <$> iter t
    cong (Val (Bang t)) | not weak = Val . Bang <$> iter t
    cong _ = Nothing

-- | Reduce the term fully, and log every step
reduceFully :: Bool -> Tm n -> Writer [Tm n] (Tm n)
reduceFully weak t = iter t where
  iter :: Tm n -> Writer [Tm n] (Tm n)
  iter t = tell [t] >> case reduce weak t of
    Nothing -> return t
    Just t' -> iter t'

compileLCbyName :: LC.Exp n -> Tm n
compileLCbyName = iter
  where
    iter :: LC.Exp n -> Tm n
    iter (LC.Var x) = Der (Val (Var x))
    iter (LC.Lam bnd) =
      let b = unbindl bnd
       in Abs . bind $ iter b
    iter (LC.App l r) = App (iter l) (Val $ Bang $ iter r)

compileLCbyValue :: LC.Exp n -> Tm n
compileLCbyValue = iter
  where
    iter :: LC.Exp n -> Tm n
    iter (LC.Var x) = Val (Var x)
    iter (LC.Lam bnd) =
      let b = unbindl bnd
       in Val . Bang . Abs . bind $ iter b
    iter (LC.App l r) = App (Der $ iter l) (iter r)

--------------------------------------------------------------------------------
--- Let's reduce some terms!
--------------------------------------------------------------------------------

t0 = lam (lam v1) @@ (lam v0 @@ bang v0)
-- >>> t0
-- <λ. λ. 1> <λ. 0> !0

-- See https://github.com/haskell/haskell-language-server/blob/master/plugins/hls-eval-plugin/README.md#multiline-output
ppLogs :: Writer [Tm n] (Tm n) -> String
ppLogs m = error $ join $ intersperse ['\n'] (show <$> execWriter m)

-- >>> ppLogs $ reduceFully False t0
-- <λ. λ. 1> <λ. 0> !0
-- <λ. λ. 1> !0
-- λ. !1

-- A term in the usual lambda calculus
l0 :: LC.Exp (S (S n))
l0 = LC.lam (LC.v0 LC.@@ LC.v0) LC.@@ (LC.lam LC.v0 LC.@@ LC.lam LC.v1)
-- >>> l0
-- ((λ. (0 0)) ((λ. 0) (λ. 1)))

-- >>> ppLogs $ reduceFully False $ compileLCbyName l0
-- <λ. <der 0> !der 0> !<λ. der 0> !λ. der 1
-- <der !<λ. der 0> !λ. der 1> !der !<λ. der 0> !λ. der 1
-- <<λ. der 0> !λ. der 1> !der !<λ. der 0> !λ. der 1
-- <der !λ. der 1> !der !<λ. der 0> !λ. der 1
-- <λ. der 1> !der !<λ. der 0> !λ. der 1
-- der 0

-- >>> ppLogs $ reduceFully False $ compileLCbyValue l0
-- <der !λ. <der 0> 0> <der !λ. 0> !λ. 1
-- <λ. <der 0> 0> <der !λ. 0> !λ. 1
-- <λ. <der 0> 0> <λ. 0> !λ. 1
-- <λ. <der 0> 0> !λ. 1
-- <der !λ. 1> !λ. 1
-- <λ. 1> !λ. 1
-- 0
