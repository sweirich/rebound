{-# LANGUAGE UndecidableSuperClasses #-}

module AutoEnv.DependentScope
  ( Sized (..),
    MonadScoped (..),
    Scope (..),
    ScopedReader (..),
    ScopedReaderT (..),
    LocalName (..),
    singleton,
    runScopedReader,
    scope,
    scopeSize,
    fromScope,
    withScopeSize,
    -- mapScope,
    push,
    push1,
    WithData (..),
  )
where

import AutoEnv.Classes (Sized (..))
import AutoEnv.Context
import AutoEnv.Env
  ( Env,
    Shiftable (..),
    Subst (..),
    SubstVar,
    applyEnv,
    fromVec,
    oneE,
    shift1E,
    shiftNE,
    singletonE,
    weakenE',
    zeroE,
    (.++),
    (.>>),
  )
import AutoEnv.Lib
import AutoEnv.MonadScoped qualified as SimpleScope
import Control.Monad.Error.Class (MonadError (..))
import Control.Monad.Identity (Identity (runIdentity))
import Control.Monad.Reader (MonadReader (ask, local))
import Control.Monad.Writer (MonadWriter (..))
import Data.Functor.Const (Const)
import Data.SNat qualified as SNat
import Data.Vec qualified as Vec
import GHC.Generics (U1 (..), (:*:))
import Prelude hiding (map)

-----------------------------------------------------------------------
-- MonadScoped class
-----------------------------------------------------------------------

-- Note that we could parametrize all subsequent definitions by an initial
-- scope. We instead make the choice of fixing the outer scope to Z. This
-- simplifies all subsequent definition, and working in a latent undefined scope
-- seems exotic and can be emulated fairly easily.
type Scope s p n = Env s p (p + n)

singleton :: forall v s n. (Subst v s) => s n -> Scope s N1 n
singleton v = let v' = applyE (shift1E @v) v in oneE @s @(S n) v'

-- | Scoped monads provide implicit access to the current scope and a way to
-- extend that scope with a new scope.
class (forall n. Monad (m n), SubstVar s, Shiftable b) => MonadScoped s b m | m -> s, m -> b where
  scope' :: m n (SNat n, Ctx s n)
  pushEnv :: (SNatI p) => Scope s p n -> m (p + n) a -> m n a
  blob :: m n (b n)
  local :: (b n -> b n) -> m n a -> m n a

scope :: (MonadScoped s b m) => m n (Ctx s n)
scope = snd <$> scope'

scopeSize :: (MonadScoped s b m) => m n (SNat n)
scopeSize = fst <$> scope'

fromScope :: forall t s b m n. (MonadScoped s b m, SubstVar s) => Fin n -> m n (s n)
fromScope i = case axiomPlusZ @n of Refl -> (`applyEnv` i) <$> scope

withScopeSize :: forall t n s b m a. (MonadScoped s b m) => ((SNatI n) => m n a) -> m n a
withScopeSize k = do
  size <- scopeSize
  withSNat size k

-- projectScope :: Scope u s n -> SimpleScope.Scope u n
-- projectScope s = let (k, v) = iter SZ s in SimpleScope.Scope k v
--   where
--     iter :: forall k u s n. SNat k -> Scope u s n -> (SNat (k + n), Vec n u)
--     iter k TNil = case axiomPlusZ @k of Refl -> (k, Vec.empty)
--     iter k (TCons @_ @_ @n' @_ (u, _) xs) =
--       case axiomSus @k @n' of
--         Refl -> let (k', xs') = withSNat k $ iter @(S k) SS xs in (k', u Vec.::: xs')

-- projectScope :: Scope u s n -> Vec n u
-- projectScope TNil = Vec.empty
-- projectScope (TCons @_ @_ @n' @_ (u, _) xs) = u Vec.::: projectScope xs

-----------------------------------------------------------------------
-- ScopedReader monad
-----------------------------------------------------------------------

-- Trivial instance of MonadScoped
type ScopedReader s b n = ScopedReaderT s b Identity n

runScopedReader :: forall t n s b a. (SubstVar s, SNatI n) => SNat n -> Ctx s n -> b n -> ScopedReader s b n a -> a
runScopedReader n d b m = runIdentity $ runScopedReaderT m (n, d, b)

-----------------------------------------------------------------------
-- ScopedReaderT monad transformer
-----------------------------------------------------------------------

-- | A monad transformer that adds a scope environment to any existing monad
-- We also cannot make it an instance of the MonadTrans class because
-- the scope size n needs to be the next-to-last argument instead of the
-- underlying monad
newtype ScopedReaderT s b m n a = ScopedReaderT {runScopedReaderT :: (SNat n, Ctx s n, b n) -> m a}
  deriving (Functor)

-- mapScope :: (Monad m) => (forall n. s n -> s' n) -> ScopedReaderT s' b m n a -> ScopedReaderT s b m n a
-- mapScope f m = ScopedReaderT $ \(k, s, b) ->
--   let s' = map f s
--    in runScopedReaderT m (k, s', b)

instance (Applicative m) => Applicative (ScopedReaderT s b m n) where
  pure f = ScopedReaderT $ \x -> pure f
  ScopedReaderT f <*> ScopedReaderT x = ScopedReaderT (\e -> f e <*> x e)

instance (Monad m) => Monad (ScopedReaderT s b m n) where
  ScopedReaderT m >>= k = ScopedReaderT $ \e ->
    m e >>= (\v -> let x = k v in runScopedReaderT x e)

-- TODO: Disabled due to name clash...
-- instance (MonadReader e m) => MonadReader e (ScopedReaderT t u s b m n) where
--   ask = ScopedReaderT $ const ask
--   local f m = ScopedReaderT (local f . runScopedReaderT m)

instance (MonadError e m) => MonadError e (ScopedReaderT s b m n) where
  throwError e = ScopedReaderT $ const (throwError e)
  catchError m k = ScopedReaderT $ \s -> runScopedReaderT m s `catchError` (\err -> runScopedReaderT (k err) s)

instance (MonadWriter w m) => MonadWriter w (ScopedReaderT s b m n) where
  writer w = ScopedReaderT $ const (writer w)
  listen m = ScopedReaderT $ \s -> listen $ runScopedReaderT m s
  pass m = ScopedReaderT $ \s -> pass $ runScopedReaderT m s

instance (Monad m, SubstVar s, Shiftable b) => MonadScoped s b (ScopedReaderT s b m) where
  scope' = ScopedReaderT $ \(u, s, _) -> return (u, s)

  -- TODO: what is going when this signature is removed?!?
  pushEnv :: forall m s b p n a. (Monad m, SubstVar s, Shiftable b, SNatI p) => Scope s p n -> ScopedReaderT s b m (p + n) a -> ScopedReaderT s b m n a
  pushEnv (v :: Scope s p n) m =
    ScopedReaderT $ \(sn, ss, sb) ->
      let p = snat @p
          sn' = sPlus p sn
          ss' = ss ++++ v -- v .++ (ss .>> shiftNE p)
          sb' = shift p sb
       in runScopedReaderT m (sn', ss', sb')
  blob = ScopedReaderT $ \(_, _, b) -> return b
  local f m = ScopedReaderT $ \(k, s, b) -> runScopedReaderT m (k, s, f b)

-----------------------------------------------------------------------
-- Extracting data from binders/patterns
-----------------------------------------------------------------------

-- | Extract data from the pattern. This typeclass should be used when the
-- binders are dependent, i.e. the data associated to a binder can refer to
-- previous binders. If you don't need scoped data, use
-- 'MonadScoped.MonadScoped' instead.
class (Sized p) => WithData (p :: Type) (s :: Nat -> Type) (n :: Nat) where
  getData :: p -> Scope s (Size p) n
  getData p = snd $ getSizeData @_ @_ @n p
  getSizeData :: p -> (SNat (Size p), Scope s (Size p) n)
  getSizeData p = (size p, getData @_ @_ @n p)

push :: forall s b m n p a. (MonadScoped s b m, WithData p s n) => p -> m (Size p + n) a -> m n a
push p = withSNat (size p) $ pushEnv (getData @p @s @n p)

push1 :: forall s b m n a. (MonadScoped s b m, SubstVar s) => s n -> m (S n) a -> m n a
push1 p = pushEnv $ oneE (applyE @s shift1E p)

-- pushu :: forall t p u s b n m a. (MonadScoped U1 b m, WithData p u s n) => p -> m (Size p + n) a -> m n a
-- pushu p = pushTelescope (map (\u _ -> (u, U1)) $ getData @_ @u @s p)

-- push1u :: (MonadScoped U1 b m) => u -> m (S n) a -> m n a
-- push1u u = pushTelescope (TCons (u, U1) TNil)