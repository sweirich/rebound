-- | Parallel substitution using a shifted list 
-- Does not cache substitutions at binders.
module DeBruijn.Skew.ShiftList (impl) where

import Control.DeepSeq
import Data.List (elemIndex)
import Util.IdInt
import Util.Impl
import qualified Util.Stats as Stats
import Util.Syntax.Lambda

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.Skew.ShiftList",
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

-- The 'Int' in 'Inc k' and 'Cons k' is an embedded shift.
-- 'Inc k' means all remaining variables are shifted by k (i.e. DVar i -> DVar (k+i)).
-- 'Cons k t rest' means: variable 0 maps to (weaken k t),
--   subsequent variables follow rest (with additional k shift accumulated).
data Env a
    = Zero
    | Inc  {-# UNPACK #-} !Int
    | Cons {-# UNPACK #-} !Int a (Env a)

instance (NFData a) => NFData (Env a) where
  rnf Zero          = ()
  rnf (Inc x)       = rnf x
  rnf (Cons x a xs) = rnf x `seq` rnf a `seq` rnf xs

type Sub = Env DB

------------------------------------------------------------------------------
-- Operations
------------------------------------------------------------------------------

-- | Apply a substitution to a variable index, accumulating shifts.
applyRec :: Int -> Sub -> Int -> DB
applyRec acc s i =
    case s of
        Zero        -> error "variable out of scope"
        Inc k       -> DVar (acc + k + i)
        Cons k t s'
            | i == 0    -> weaken (acc + k) t
            | otherwise -> applyRec (acc + k) s' (i - 1)
{-# INLINEABLE applyRec #-}

applySub :: Sub -> Int -> DB
applySub = applyRec 0
{-# INLINEABLE applySub #-}

-- | Shift all free variables in a term by k.
weaken :: Int -> DB -> DB
weaken 0 t = t
weaken k t = subst (Inc k) t
{-# INLINEABLE weaken #-}

-- | Identity substitution.
idSub :: Sub
idSub = Inc 0
{-# INLINEABLE idSub #-}

-- | Substitution replacing variable 0 with t, leaving others unchanged.
single :: DB -> Sub
single t = Cons 0 t idSub
{-# INLINEABLE single #-}

-- | Add k to the shift at the head of the substitution.
skip :: Int -> Sub -> Sub
skip k Zero          = Zero
skip k (Inc k2)      = Inc (k + k2)
skip k (Cons k2 t s) = Cons (k + k2) t s
{-# INLINEABLE skip #-}

-- | Lift a substitution under one binder.
up :: Sub -> Sub
up s = Cons 0 (DVar 0) (skip 1 s)
{-# INLINEABLE up #-}

instantiate :: DB -> DB -> DB
instantiate b a = subst (single a) b
{-# INLINEABLE instantiate #-}

substBind :: Sub -> DB -> DB
substBind s = subst (up s)
{-# INLINEABLE substBind #-}

-- | Compose two substitutions: apply s1 then s2.
comp :: Sub -> Sub -> Sub
comp Zero _                      = Zero
comp s    (Inc k)                = skip k s
comp (Inc 0) s                   = s
comp (Inc k) (Cons k2 _ xs)      = comp (Inc (k - 1)) (skip k2 xs)
comp (Cons k x xs) s             = Cons 0 (subst (comp (Inc k) s) x) (comp (skip k xs) s)
comp (Inc k) Zero                = error "comp: this case should be impossible"
{-# INLINEABLE comp #-}

-- | Map the range of an environment.
transform :: (a -> b) -> Env a -> Env b
transform _ Zero          = Zero
transform _ (Inc k)       = Inc k
transform f (Cons k x xs) = Cons k (f x) (transform f xs)
