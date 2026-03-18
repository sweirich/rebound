-- | Parallel substitutions, represented using Skew binary trees
-- https://mathisbd.github.io/blog/esubstitutions.html
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
module DeBruijn.Skew.CompSkewList (impl) where

import Control.DeepSeq
import Data.List (elemIndex)
import Util.IdInt
import Util.Impl
import qualified Util.Stats as Stats
import Util.Syntax.Lambda

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.Skew.CompSkewList",
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

----------------------------------------------------------

data Tree = Leaf
  { leaf_k :: !Int,
    leaf_t :: !DB
  }
  | Node
      { node_k :: !Int,
        node_k_tot :: !Int,
        node_t :: !DB,
        node_left :: Tree,
        node_right :: Tree
      }

--  type subst = Nil of int | Cons of int * tree * subst

data List = Nil !Int | Cons !Int Tree List

data Sub = Sub [List] List   -- | nonempty snoc list

totalOffset :: Tree -> Int
totalOffset (Leaf { leaf_k }) = leaf_k
totalOffset (Node { node_k_tot }) = node_k_tot

leaf :: DB -> Tree
leaf t = Leaf { leaf_k = 0, leaf_t = t }

node :: DB -> Tree -> Tree -> Tree
node t left right =
  Node
    { node_k = 0,
      node_k_tot = totalOffset left + totalOffset right,
      node_t = t,
      node_left = left,
      node_right = right
    }

applyTree :: Int -> Int -> Tree -> Int -> DB
applyTree acc n (Leaf { leaf_k, leaf_t }) i = weaken (acc + leaf_k) leaf_t
applyTree acc n (Node { node_k, node_t, node_left, node_right, node_k_tot }) i
  | i == 0 = weaken (acc + node_k) node_t
  | i <= n `div` 2 = applyTree (acc + node_k) (n `div` 2) node_left (i - 1)
  | otherwise = applyTree (acc + node_k + totalOffset node_left)
                     (n `div` 2) node_right (i - 1 - (n `div` 2))

weaken :: Int -> DB -> DB
weaken x e = subst (shiftSub x) e

applyRec :: Int -> List -> Int -> DB
applyRec acc (Nil k) i = DVar (i + k + acc)
applyRec acc (Cons n t s) i
  | i < n = applyTree acc n t i
  | otherwise = applyRec (acc + totalOffset t) s (i - n)

applyList :: List -> Int -> DB
applyList s i = applyRec 0 s i

applySub :: Sub -> Int -> DB
applySub (Sub [] s) i = applyRec 0 s i
applySub (Sub (t:ts) s) i = 
  subst (Sub [] t) (applySub (Sub ts s) i)
{-# INLINE applySub #-}

-- let id : subst = Nil 0
idSub :: Sub
idSub = Sub [] (Nil 0)
{-# INLINE idSub #-}

shiftSub :: Int -> Sub
shiftSub k = Sub [] (Nil k)
{-# INLINE shiftSub #-}

-- singleton, replace 0 with t, leave everything
-- else alone
single :: DB -> Sub
{-# INLINE single #-}
single t = t `consSub` idSub

-- | extend the substitution by consing a new tree for variable 0
consList :: DB -> List -> List
{-# INLINE consList #-}
consList x (Cons n1 t1 (Cons n2 t2 tail))
  | n1 == n2 = Cons (1 + n1 + n2) (node x t1 t2) tail
consList x s = Cons 1 (leaf x) s

-- | extend the substitution
consSub :: DB -> Sub -> Sub
{-# INLINE consSub #-}
consSub x s = 
  let Sub [] s' = compress s in
    Sub [] (consList x s')


compList :: List -> List -> List
compList s (Nil k) = skip k s 
compList (Nil 0) s = s
compList (Nil k) (Cons k2 t s) = comp (Nil (k-1)) undefined undefined
compList (Cons k t ss) s = Cons 0 (applyList (comp (Nil k) s) 

comp Zero _                      = Zero
comp s    (Inc k)                = skip k s
comp (Inc 0) s                   = s
comp (Inc k) (Cons k2 _ xs)      = comp (Inc (k - 1)) (skip k2 xs)
comp (Cons k x xs) s             = Cons 0 (subst (comp (Inc k) s) x) (comp (skip k xs) s)
comp (Inc k) Zero                = error "comp: this case should be impossible"
{-# INLINEABLE comp #-}

compress :: Sub -> Sub
compress (Sub [] s) = Sub [] s
compress (Sub (t:ts) s) = 
  let (Sub [] s') = compress (Sub ts s) in
    (Sub [] (comp t s'))


skipTree :: Int -> Tree -> Tree
skipTree k0 (Leaf { leaf_k, leaf_t }) = Leaf { leaf_k = leaf_k + k0, leaf_t }
skipTree k0 (Node { node_k, node_k_tot, node_t, node_left, node_right }) =
    Node { node_k = node_k + k0, node_k_tot = node_k_tot + k0, node_t, node_left, node_right }

skip :: Int -> List -> List
skip k0 (Nil k) = Nil (k0 + k)
skip k0 (Cons n t s) = Cons n (skipTree k0 t) s

consVars :: Int -> Sub -> Sub
consVars n s
  | n <= 0 = s
  | otherwise = consVars (n - 1) (consSub (DVar (n - 1)) s)

up :: Int -> Sub -> Sub
up k0 s = consVars k0 (skip k0 s)
{-# INLINE up #-}

instantiate :: DB -> DB -> DB
instantiate b a = subst (single a) b
{-# INLINEABLE instantiate #-}

substBind :: Sub -> DB -> DB
substBind s = subst (up 1 s)
{-# INLINEABLE substBind #-}
