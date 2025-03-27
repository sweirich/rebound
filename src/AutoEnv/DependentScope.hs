{-# LANGUAGE UndecidableSuperClasses #-}

module AutoEnv.DependentScope
  ( Sized (..),
    MonadScoped (..),
    Telescope (..),
    Scope (..),
    ScopedReader (..),
    ScopedReaderT (..),
    LocalName (..),
    fromTelescope,
    append,
    runScopedReader,
    empty,
    singleton,
    projectScope,
    scope,
    scopeSize,
    fromScope,
    withScopeSize,
    mapScope,
    push,
    push1,
    pushu,
    push1u,
    WithData (..),
  )
where

import AutoEnv.Classes (Sized (..))
import AutoEnv.Context
import AutoEnv.Env (Env, Subst (..), SubstVar, fromVec, shiftNE, weakenE', zeroE, (.++), (.>>), Shiftable (..))
import AutoEnv.Lib
import AutoEnv.MonadScoped qualified as SimpleScope
import Control.Monad.Error.Class (MonadError (..))
import Control.Monad.Identity (Identity (runIdentity))
import Control.Monad.Reader (MonadReader (ask, local))
import Control.Monad.Writer (MonadWriter (..))
import Data.SNat qualified as SNat
import Data.Scoped.Const
import Data.Vec qualified as Vec
import Prelude hiding (map)

-----------------------------------------------------------------------
-- Scopes
-----------------------------------------------------------------------

-- | Unlike 'Scoped.TeleList', this datatype does not nest: it is effectively a
-- 'List'/'Vec' but with extra scoping inside.
data Telescope u s n m where
  TNil :: Telescope u s Z m
  TCons :: (u, s (n + m)) -> !(Telescope u s n m) -> Telescope u s (S n) m

map :: (forall k. u -> s k -> (u', s' k)) -> Telescope u s n m -> Telescope u' s' n m
map f TNil = TNil
map f (TCons (u, s) xs) = TCons (f u s) (map f xs)

empty :: Telescope u s Z m
empty = TNil

singleton :: (u, s n) -> Telescope u s (S Z) n
singleton h = TCons h TNil

append :: forall u s nl nr m. Telescope u s nl (nr + m) -> Telescope u s nr m -> (SNat nl, Telescope u s (nl + nr) m)
append TNil r = (SZ, r)
append (TCons l ls) r =
  case axiomAssoc @nl @nr @m of
    Refl -> let (k, ls') = append ls r in withSNat k (SS, TCons l ls')

toTelescope :: forall p n u s. (Shiftable s) => Vec p (u, s n) -> Telescope u s p n
toTelescope = snd . iter
  where
    iter :: forall p. Vec p (u, s n) -> (SNat p, Telescope u s p n)
    iter Vec.VNil = (SZ, TNil)
    iter ((Vec.:::) @_ @p' (u, s) xs) =
      let (sp', sc') :: (SNat p', Telescope u s p' n) = iter xs
          s' :: s (p' + n) = shift sp' s
       in (withSNat sp' SS, TCons (u, s') sc')

fromTelescope :: forall s u p n. (Shiftable s) => Telescope u s p n -> (SNat p, Vec p (u, s (p + n)))
fromTelescope = iter SZ
  where
    iter :: forall u s k n m. (Shiftable s) => SNat k -> Telescope u s n m -> (SNat (k + n), Vec n (u, s (k + n + m)))
    iter sk TNil = case axiomPlusZ @k of Refl -> (sk, Vec.empty)
    iter sk (TCons @_ @_ @n' (u, s) sc) =
      case axiomSus @k @n' of
        Refl ->
          let x' :: (u, s (k + n + m)) = case axiomAssoc @k @n' @m of Refl -> (u, shift (addOne sk) s)
              (sn', sc') :: (SNat (k + n), Vec n' (u, s (k + n + m))) = iter (addOne sk) sc
           in (sn', x' Vec.::: sc')

    addOne :: SNat k -> SNat (S k)
    addOne k = withSNat k SS

emptyTelescope = TNil

nth :: forall s n m u. (Shiftable s) => Fin n -> Telescope u s n m -> (u, s (n + m))
nth i s = snd (fromTelescope s) Vec.! i

instance Sized (Telescope u s n m) where
  type Size (Telescope u s n m) = n
  size :: Telescope u s n m -> SNat n
  size TNil = s0
  size (TCons _ t) = withSNat (size t) SS

-----------------------------------------------------------------------
-- MonadScoped class
-----------------------------------------------------------------------

-- Note that we could parametrize all subsequent definitions by an initial
-- scope. We instead make the choice of fixing the outer scope to Z. This
-- simplifies all subsequent definition, and working in a latent undefined scope
-- seems exotic and can be emulated fairly easily.
type Scope u s n = Telescope u s n Z

-- | Scoped monads provide implicit access to the current scope and a way to
-- extend that scope with a vector containing new names. Note that the API
-- doesn't rely on 'Telescope' too much, so this API could be tweak to
-- completely hide that type, allowing for instances with weaker scoping
-- enforcement, e.g. using 'Vec n' either for simplicity or to allow (mutually)
-- recursive definitions.
class (forall n. Monad (m n), Shiftable s, Shiftable b) => MonadScoped u s b m | m -> u, m -> s, m -> b where
  scope' :: m n (SNat n, Scope u s n)
  pushTelescope :: Telescope u s p n -> m (p + n) a -> m n a
  blob :: m n (b n)
  local :: (b n -> b n) -> m n a -> m n a

scope :: (MonadScoped u s b m) => m n (Scope u s n)
scope = snd <$> scope'

scopeSize :: (MonadScoped u s b m) => m n (SNat n)
scopeSize = fst <$> scope'

fromScope :: forall t u s b m n. (MonadScoped u s b m) => Fin n -> m n (u, s n)
fromScope i = case axiomPlusZ @n of Refl -> nth i <$> scope

withScopeSize :: forall t n u s b m a. (MonadScoped u s b m) => ((SNatI n) => m n a) -> m n a
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

projectScope :: Scope u s n -> Vec n u
projectScope TNil = Vec.empty
projectScope (TCons @_ @_ @n' @_ (u, _) xs) = u Vec.::: projectScope xs

-----------------------------------------------------------------------
-- ScopedReader monad
-----------------------------------------------------------------------

-- Trivial instance of MonadScoped
type ScopedReader u s b n = ScopedReaderT u s b Identity n

runScopedReader :: forall t n u s b a. (SubstVar s, SNatI n) => Scope u s n -> b n -> ScopedReader u s b n a -> a
runScopedReader d b m = runIdentity $ runScopedReaderT m (size d, d, b)

-----------------------------------------------------------------------
-- ScopedReaderT monad transformer
-----------------------------------------------------------------------

-- | A monad transformer that adds a scope environment to any existing monad
-- We also cannot make it an instance of the MonadTrans class because
-- the scope size n needs to be the next-to-last argument instead of the
-- underlying monad
newtype ScopedReaderT u s b m n a = ScopedReaderT {runScopedReaderT :: (SNat n, Scope u s n, b n) -> m a}
  deriving (Functor)

mapScope :: (Monad m) => (forall n. u -> s n -> (u', s' n)) -> ScopedReaderT u' s' b m n a -> ScopedReaderT u s b m n a
mapScope f m = ScopedReaderT $ \(k, s, b) ->
  let s' = map f s
   in runScopedReaderT m (k, s', b)

instance (Applicative m) => Applicative (ScopedReaderT u s b m n) where
  pure f = ScopedReaderT $ \x -> pure f
  ScopedReaderT f <*> ScopedReaderT x = ScopedReaderT (\e -> f e <*> x e)

instance (Monad m) => Monad (ScopedReaderT u s b m n) where
  ScopedReaderT m >>= k = ScopedReaderT $ \e ->
    m e >>= (\v -> let x = k v in runScopedReaderT x e)

-- TODO: Disabled due to name clash...
-- instance (MonadReader e m) => MonadReader e (ScopedReaderT t u s b m n) where
--   ask = ScopedReaderT $ const ask
--   local f m = ScopedReaderT (local f . runScopedReaderT m)

instance (MonadError e m) => MonadError e (ScopedReaderT u s b m n) where
  throwError e = ScopedReaderT $ const (throwError e)
  catchError m k = ScopedReaderT $ \s -> runScopedReaderT m s `catchError` (\err -> runScopedReaderT (k err) s)

instance (MonadWriter w m) => MonadWriter w (ScopedReaderT u s b m n) where
  writer w = ScopedReaderT $ const (writer w)
  listen m = ScopedReaderT $ \s -> listen $ runScopedReaderT m s
  pass m = ScopedReaderT $ \s -> pass $ runScopedReaderT m s

instance (Monad m, Shiftable s, Shiftable b) => MonadScoped u s b (ScopedReaderT u s b m) where
  scope' = ScopedReaderT $ \(u, s, _) -> return (u, s)
  pushTelescope (v :: Telescope u s p n) m =
    case axiomPlusZ @n of
      Refl -> ScopedReaderT $ \(sz, ss, sb) ->
        let (k, s) = append @_ @_ @p @n v ss
            sb' = shift k sb
         in runScopedReaderT m (sPlus k sz, s, sb')
  blob = ScopedReaderT $ \(_, _, b) -> return b
  local f m = ScopedReaderT $ \(k, s, b) -> runScopedReaderT m (k, s, f b)

-----------------------------------------------------------------------
-- Extracting data from binders/patterns
-----------------------------------------------------------------------

-- | Extract data from the pattern. This typeclass should be used when the
-- binders are dependent, i.e. the data associated to a binder can refer to
-- previous binders. If you don't need scoped data, use
-- 'MonadScoped.MonadScoped' instead.
class (Sized p) => WithData p u s m where
  getData :: p -> Telescope u s (Size p) m

fromScopedData :: (Shiftable s) => Vec p (u, s m) -> Telescope u s p m
fromScopedData = toTelescope

push :: (MonadScoped u s b m, WithData p u s n) => p -> m (Size p + n) a -> m n a
push p = pushTelescope (getData p)

push1 :: (MonadScoped u s b m) => (u, s n) -> m (S n) a -> m n a
push1 p = pushTelescope (TCons p TNil)

pushu :: forall t p u s b n m a. (MonadScoped u Const b m, WithData p u s n) => p -> m (Size p + n) a -> m n a
pushu p = pushTelescope (map (\u _ -> (u, Const)) $ getData @_ @u @s p)

push1u :: (MonadScoped u Const b m) => u -> m (S n) a -> m n a
push1u u = pushTelescope (TCons (u, Const) TNil)