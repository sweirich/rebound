-- | Parallel substitution using non-dependent version of "Lazy" from rebound
-- Does not cache substitutions at binders.
module DeBruijn.Skew.Lazy (impl) where

import Control.DeepSeq
import Data.List (elemIndex)
import Util.IdInt
import Util.Impl
import qualified Util.Stats as Stats
import Util.Syntax.Lambda

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.Skew.Lazy",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = nfi,
      impl_aeq = (==),
      impl_eval = whnf
    }

data DB
  = DVar {-# UNPACK #-} !Int
  | DLam !DB
  | DApp !DB !DB
  | DBool !Bool
  | DIf !DB !DB !DB
  deriving (Eq)

instance NFData DB where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b
  rnf (DBool b) = rnf b
  rnf (DIf c t f) = rnf c `seq` rnf t `seq` rnf f
----------------------------------------------------------

subst :: Sub -> DB -> DB
subst s = go
  where
    go (DVar i) = applySub s i
    go (DLam e) = DLam (substBind s e)
    go (DApp f a) = DApp (go f) (go a)
    go (DBool b) = DBool b
    go (DIf c t f) = DIf (go c) (go t) (go f)
----------------------------------------------------------

nf :: DB -> DB
nf e@(DVar _) = e
nf (DLam e) = DLam (nf e)
nf (DApp f a) =
  case whnf f of
    DLam b -> nf (instantiate b a)
    f' -> DApp (nf f') (nf a)
nf (DBool b) = DBool b
nf (DIf c t f) =
  case whnf c of
    DBool True -> nf t
    DBool False -> nf f
    c' -> DIf c' (nf t) (nf f)

whnf :: DB -> DB
whnf e@(DVar _) = e
whnf e@(DLam _) = e
whnf (DApp f a) =
  case whnf f of
    DLam b -> whnf (instantiate b a)
    f' -> DApp f' a
whnf (DBool b) = DBool b
whnf (DIf c t f) =
  case whnf c of
    DBool True -> whnf t
    DBool False -> whnf f
    c' -> DIf c' t f

----------------------------------------------------------

nfi :: Int -> DB -> Stats.M DB
nfi 0 _e = Stats.done
nfi _n e@(DVar _) = return e
nfi n (DLam b) = DLam <$> nfi (n -1) b
nfi n (DApp f a) = do
  f' <- whnfi (n -1) f
  case f' of
    DLam b -> Stats.count >> nfi (n -1) (instantiate b a)
    _ -> DApp <$> nfi n f' <*> nfi n a
nfi n (DBool b) = return $ DBool b
nfi n (DIf c t f) = do
  c' <- whnfi (n -1) c
  case c' of
    DBool True -> nfi (n -1) t
    DBool False -> nfi (n -1) f
    _ -> DIf <$> nfi n c' <*> nfi n t <*> nfi n f

whnfi :: Int -> DB -> Stats.M DB
whnfi 0 _e = Stats.done
whnfi _n e@(DVar _) = return e
whnfi _n e@(DLam _) = return e
whnfi n (DApp f a) = do
  f' <- whnfi (n -1) f
  case whnf f' of
    DLam b -> Stats.count >> whnfi (n -1) (instantiate b a)
    _ -> return $ DApp f' a
whnfi n (DBool b) = return $ DBool b
whnfi n (DIf c t f) = do
  c' <- whnfi (n -1) c
  case whnf c' of
    DBool True -> whnfi (n -1) t
    DBool False -> whnfi (n -1) f
    _ -> return $ DIf c' t f

----------------------------------------------------------

toDB :: LC IdInt -> DB
toDB = to []
  where
    to vs (Var v@(IdInt i)) = maybe (DVar i) DVar (elemIndex v vs)
    to vs (Lam x b) = DLam (to (x : vs) b)
    to vs (App f a) = DApp (to vs f) (to vs a)
    to vs (Bool b) = DBool b
    to vs (If c t f) = DIf (to vs c) (to vs t) (to vs f)

fromDB :: DB -> LC IdInt
fromDB = from firstBoundId
  where
    from (IdInt n) (DVar i)
      | i < 0 = Var (IdInt i)
      | i >= n = Var (IdInt i)
      | otherwise = Var (IdInt (n - i -1))
    from n (DLam b) = Lam n (from (succ n) b)
    from n (DApp f a) = App (from n f) (from n a)
    from n (DBool b) = Bool b
    from n (DIf c t f) = If (from n c) (from n t) (from n f)

------------------------------------------------------------------------------
-- Environment representation
------------------------------------------------------------------------------

-- | Substitution mapping variables to terms.
--   Inc k:    variable i maps to DVar (k + i) (shift by k; Inc 0 is identity)
--   Cons t s: variable 0 maps to t, rest follows s
--   s1 :<> s2: apply s1 then s2 (lazy composition)
data Env a
    = Zero
    | Inc   {-# UNPACK #-} !Int
    | Cons a (Env a)
    | (Env a) :<> (Env a)

instance (NFData a) => NFData (Env a) where
  rnf Zero        = ()
  rnf (Inc m)     = rnf m
  rnf (Cons x r)  = rnf x `seq` rnf r
  rnf (r1 :<> r2) = rnf r1 `seq` rnf r2

type Sub = Env DB

------------------------------------------------------------------------------
-- Application
------------------------------------------------------------------------------

-- | Apply an environment to a variable index.
applyEnv :: Sub -> Int -> DB
applyEnv Zero _        = error "variable out of scope"
applyEnv (Inc m) i     = DVar (m + i)
applyEnv (Cons t _) 0  = t
applyEnv (Cons _ s) i  = applyEnv s (i - 1)
applyEnv (s1 :<> s2) i = subst s2 (applyEnv s1 i)
{-# INLINEABLE applyEnv #-}

applySub :: Sub -> Int -> DB
applySub = applyEnv
{-# INLINEABLE applySub #-}

-- | Skip identity substitutions before applying.
applyOpt :: (Sub -> DB -> DB) -> (Sub -> DB -> DB)
applyOpt _ (Inc 0) x = x
applyOpt f r       x = f r x
{-# INLINEABLE applyOpt #-}

------------------------------------------------------------------------------
-- Construction and modification
------------------------------------------------------------------------------

-- | The empty environment (zero domain).
zeroE :: Sub
zeroE = Zero
{-# INLINEABLE zeroE #-}

-- | Shift all variables up by m.
shiftNE :: Int -> Sub
shiftNE = Inc
{-# INLINEABLE shiftNE #-}

-- | Extend an environment with a new mapping for variable 0.
(.:) :: DB -> Sub -> Sub
(.:) = Cons
{-# INLINEABLE (.:) #-}

-- | Remove the mapping for variable 0.
tail :: Sub -> Sub
tail x = shiftNE 1 .>> x
{-# INLINEABLE tail #-}

-- | Compose two environments (left then right).
(.>>) :: Sub -> Sub -> Sub
(.>>) = comp
{-# INLINEABLE (.>>) #-}

-- | Compose two environments with optimizations.
comp :: Sub -> Sub -> Sub
comp Zero _                             = Zero
comp (Inc k1) (Inc k2)                 = Inc (k2 + k1)
comp s (Inc k)     | k == 0            = s
comp (Inc k) s     | k == 0            = s
comp (Inc k) (Cons _ p) | k > 0        = comp (Inc (k - 1)) p
comp (s1 :<> s2) s3                    = comp s1 (comp s2 s3)
comp (Cons t s1) s2                    = Cons (subst s2 t) (comp s1 s2)
comp s1 s2                             = s1 :<> s2
{-# INLINEABLE comp #-}

-- | Lift an environment under one binder.
up :: Sub -> Sub
up (Inc 0) = Inc 0
up e       = DVar 0 .: comp e (Inc 1)
{-# INLINEABLE up #-}

instantiate :: DB -> DB -> DB
instantiate b a = subst (Cons a (Inc 0)) b
{-# INLINEABLE instantiate #-}

substBind :: Sub -> DB -> DB
substBind s = subst (up s)
{-# INLINEABLE substBind #-}
