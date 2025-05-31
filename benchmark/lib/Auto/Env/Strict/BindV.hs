{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}


-- | Uses the Rebound library, with a lazy datatype
-- The whnf function does not include an explicit environment argument
module Auto.Env.Strict.BindV (toDB, impl) where

import Rebound
import Rebound.Bind.Single
import Data.Fin
import Control.DeepSeq (NFData (..))
import Data.Maybe (fromJust)
import Text.PrettyPrint.HughesPJ
  ( Doc,
    parens,
    renderStyle,
    style,
    text,
    (<+>),
  )
import qualified Text.PrettyPrint.HughesPJ as PP
import Util.IdInt (IdInt (..), firstBoundId)
import Util.Impl (LambdaImpl (..))
import qualified Util.Stats as Stats
import Util.Syntax.Lambda (LC (..))

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Auto.Env.Strict.BindV",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "nfi unimplemented",
      impl_aeq = (==),
      impl_eval = eval
    }

data DB n where
  DVar :: !(Fin n) -> DB n
  DLam :: !(Bind DB DB n) -> DB n
  DApp :: !(DB n) -> !(DB n) -> DB n
  DBool :: {-# UNPACK #-} !Bool -> DB n
  DIf :: !(DB n) -> !(DB n) -> !(DB n) -> DB n
-- standalone b/c GADT
-- alpha equivalence is (==)
deriving instance SNatI n =>  Eq (DB n)

instance SNatI n => Eq (Bind DB DB n) where
  b1 == b2 = getBody b1 == getBody b2

instance SNatI a => NFData (DB a) where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b
  rnf (DBool b) = rnf b
  rnf (DIf a b c) = rnf a `seq` rnf b `seq` rnf c

instance (Subst v e, Subst v v, forall n. SNatI n => NFData (e n), SNatI n) => NFData (Bind v e n) where
  rnf b = rnf (getBody b)

----------------------------------------------------------
-- uses the SubstScoped library
instance SubstVar DB where
  var = DVar
  {-# INLINEABLE var #-}

instance Subst DB DB where
  applyE s (DVar i) = applyEnv s i
  applyE s (DLam b) = DLam (applyE s b)
  applyE s (DApp f a) = DApp (applyE s f) (applyE s a)
  applyE s (DIf a b c) = DIf (applyE s a) (applyE s b) (applyE s c)
  applyE s (DBool b) = DBool b
  {-# INLINEABLE applyE #-}

{-# SPECIALIZE idE ::Env DB n n #-}

{-# SPECIALIZE (.>>) :: Env DB m n -> Env DB n p -> Env DB m p #-}

{-# SPECIALIZE up ::  Env DB n m -> Env DB ('S n) ('S m) #-}

{-# SPECIALIZE getBody ::  Bind DB DB n -> DB ('S n) #-}

{-# SPECIALIZE instantiate ::  Bind DB DB n -> DB n -> DB n #-}

{-# SPECIALIZE bind :: DB (S n) -> Bind DB DB n #-}

----------------------------------------------------------

-- Computing the normal form proceeds as usual.

nf :: SNatI n => DB n -> DB n
nf e@(DVar _) = e
nf (DLam b) = DLam (bind (nf (getBody b)))
nf (DApp f a) =
  case whnf f of
    DLam b -> nf (instantiate b (whnf a))
    f' -> DApp (nf f') (nf a)
nf e@(DBool _) = e
nf (DIf a b c) = 
  case whnf a of 
    DBool True -> nf a
    DBool False -> nf b
    a' -> DIf (nf a) (nf b) (nf c)

whnf :: DB n -> DB n
whnf e@(DVar _) = e
whnf e@(DLam _) = e
whnf (DApp f a) =
  case whnf f of
    DLam b -> whnf (instantiate b (whnf a))
    f' -> DApp f' a
whnf e@(DBool b) = DBool b
whnf (DIf a b c) = 
  case whnf a of 
    DBool True -> whnf b
    DBool False -> whnf c
    a' -> DIf a' b c
    


eval :: DB n -> DB n
eval e@(DVar _) = e
eval e@(DLam _) = e
eval (DApp f a) =
  case eval f of
    DLam b -> eval (instantiate b (eval a))
    f' -> f' 
eval (DBool b) = DBool b
eval (DIf a b c) = 
  case eval a of 
    DBool True -> eval b
    DBool False -> eval c
    a' -> DIf a' b c

---------------------------------------------------------------

---------------------------------------------------------
{-
Convert to deBruijn indicies.  Do this by keeping a list of the bound
variable so the depth can be found of all variables. NOTE: input term
must be closed or 'fromJust' will error.
-}

toDB :: LC IdInt -> DB 'Z
toDB = to []
  where
    to :: SNatI n => [(IdInt, Fin n)] -> LC IdInt -> DB n
    to vs (Var v) = DVar (fromJust (lookup v vs))
    to vs (Lam v b) = DLam (bind b')
      where
        b' = to ((v, f0) : mapSnd fs vs) b
    to vs (App f a) = DApp (to vs f) (to vs a)
    to vs (Bool b)  = DBool b
    to vs (If a b c) = DIf (to vs a) (to vs b) (to vs c)
-- Convert back from deBruijn to the LC type.

fromDB :: SNatI n => DB n -> LC IdInt
fromDB = from firstBoundId
  where
    from :: SNatI n => IdInt -> DB n -> LC IdInt
    from (IdInt n) (DVar i)
      | toInt i < 0 = Var (IdInt $ toInt i)
      | toInt i >= n = Var (IdInt $ toInt i)
      | otherwise = Var (IdInt (n - toInt i - 1))
    from n (DLam b) = Lam n (from (Prelude.succ n) (getBody b))
    from n (DApp f a) = App (from n f) (from n a)
    from n (DBool b) = Bool b
    from n (DIf a b c) = If (from n a) (from n b) (from n c)

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(v, i) -> (v, f i))

---------------------------------------------------------

instance SNatI n => Show (DB n) where
  show = renderStyle style . ppLC 0

ppLC :: SNatI n => Int -> DB n -> Doc
ppLC _ (DVar v) = text $ "x" ++ show v
ppLC p (DLam b) = pparens (p > 0) $ text "\\." PP.<> ppLC 0 (getBody b)
ppLC p (DApp f a) = pparens (p > 1) $ ppLC 1 f <+> ppLC 2 a

pparens :: Bool -> Doc -> Doc
pparens True d = parens d
pparens False d = d
