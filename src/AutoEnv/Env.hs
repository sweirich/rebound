{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Module      : AutoEnv.Env
-- Description : Environments
-- Stability   : experimental
module AutoEnv.Env
  ( Env,
    applyEnv,
    SubstVar (..),
    Subst (..),
    GSubst (..),
    Shiftable (..),
    gapplyE,
    applyOpt,
    transform,
    zeroE,
    oneE,
    singletonE,
    idE,
    (.>>),
    (.:),
    (.++),
    head,
    tail,
    appendE,
    up,
    upN,
    shift1E,
    shiftNE,
    fromVec,
    Refinement (..),
    emptyR,
    joinR,
    singletonR,
    fromRefinement,
    toRefinement,
    refine,
    tabulate,
    fromTable,
    weakenE',
    weakenER,
    refines,
    domain,
    shiftFromApplyE,
  )
where

import AutoEnv.Lib
-- import AutoEnv.Classes

import Control.Monad
import Data.Fin (Fin (..))
import Data.Fin qualified as Fin
import Data.FinAux qualified as Fin
import Data.Map qualified as Map
import Data.Vec qualified as Vec
import GHC.Generics hiding (S)
import Prelude hiding (head, tail)

-- type Env a n m = Fin n -> a m

data Env (a :: Nat -> Type) (n :: Nat) (m :: Nat) where
  Zero :: Env a Z n
  WeakR :: !(SNat m) -> Env a n (n + m) --  weaken values in range by m
  Weak :: !(SNat m) -> Env a n (m + n) --  weaken values in range by m
  Inc :: !(SNat m) -> Env a n (m + n) --  increment values in range (shift) by m
  Cons :: (a m) -> !(Env a n m) -> Env a ('S n) m --  extend a substitution (like cons)
  (:<>) :: !(Env a m n) -> !(Env a n p) -> Env a m p --  compose substitutions

applyEnv :: (SubstVar a) => Env a n m -> Fin n -> a m
applyEnv Zero x = case x of {}
applyEnv (Inc m) x = var (Fin.shiftN m x)
applyEnv (WeakR m) x = var (Fin.weakenFinRight m x)
applyEnv (Weak m) x = var (Fin.weakenFin m x)
applyEnv (Cons ty _s) FZ = ty
applyEnv (Cons _ty s) (FS x) = applyEnv s x
applyEnv (s1 :<> s2) x = applyE s2 (applyEnv s1 x)
{-# INLINEABLE applyEnv #-}

-- | smart constructor for composition
comp ::
  forall a m n p.
  (SubstVar a) =>
  Env a m n ->
  Env a n p ->
  Env a m p
comp Zero s = Zero
comp (Weak (k1 :: SNat m1)) (Weak (k2 :: SNat m2)) =
  case axiomAssoc @m2 @m1 @m of
    Refl -> Weak (sPlus k2 k1)
comp (Weak SZ) s = s
comp s (Weak SZ) = s
comp (WeakR (k1 :: SNat m1)) (WeakR (k2 :: SNat m2)) =
  case axiomAssoc @m @m1 @m2 of
    Refl -> WeakR (sPlus k1 k2)
comp (WeakR SZ) s =
  case axiomPlusZ @m of
    Refl -> s
comp s (WeakR SZ) =
  case axiomPlusZ @n of
    Refl -> s
comp (Inc (k1 :: SNat m1)) (Inc (k2 :: SNat m2)) =
  case axiomAssoc @m2 @m1 @m of
    Refl -> Inc (sPlus k2 k1)
comp s (Inc SZ) = s
comp (Inc SZ) s = s
comp (Inc (snat_ -> SS_ p1)) (Cons _t p) = comp (Inc p1) p
comp (s1 :<> s2) s3 = comp s1 (comp s2 s3)
comp (Cons t s1) s2 = Cons (applyE s2 t) (comp s1 s2)
comp s1 s2 = s1 :<> s2
{-# INLINEABLE comp #-}

-- | mapping operation for range
-- TODO: does Conor have a name for this?
transform :: (forall m. a m -> b m) -> Env a n m -> Env b n m
transform f Zero = Zero
transform f (Weak x) = Weak x
transform f (WeakR x) = WeakR x
transform f (Inc x) = Inc x
transform f (Cons a r) = Cons (f a) (transform f r)
transform f (r1 :<> r2) = transform f r1 :<> transform f r2

----------------------------------------------------------
-- Substitution, free variables
----------------------------------------------------------

-- | Well-scoped types that can be the range of
-- an environment. This should generally be the `Var`
-- constructor from the syntax.
class (Subst v v) => SubstVar (v :: Nat -> Type) where
  var :: Fin n -> v n

class Shiftable t where
  shift :: SNat k -> t n -> t (k + n)
  default shift :: forall v k n. (SubstVar v, Subst v t) => SNat k -> t n -> t (k + n)
  shift = shiftFromApplyE @v

shiftFromApplyE :: forall v c k n. (SubstVar v, Subst v c) => SNat k -> c n -> c (k + n)
shiftFromApplyE k = applyE @v (shiftNE k)

-- | Apply the environment throughout a term of
-- type `c n`, replacing variables with values
-- of type `v m`
class (SubstVar v) => Subst v c where
  applyE :: Env v n m -> c n -> c m
  default applyE :: (Generic1 c, GSubst v (Rep1 c), SubstVar v) => Env v m n -> c m -> c n
  applyE = gapplyE
  {-# INLINE applyE #-}

gapplyE :: (Generic1 c, GSubst v (Rep1 c), SubstVar v) => Env v m n -> c m -> c n
gapplyE = applyOpt (\s x -> to1 $ gsubst s (from1 x))
{-# INLINEABLE gapplyE #-}

-- check for identity substitution
applyOpt :: (Env v n m -> c n -> c m) -> (Env v n m -> c n -> c m)
applyOpt f (Inc SZ) x = x
applyOpt f (Weak SZ) x = x
applyOpt f (WeakR SZ) (x :: c m) =
  case axiomPlusZ @m of Refl -> x
applyOpt f r x = f r x
{-# INLINEABLE applyOpt #-}

----------------------------------------------
-- operations on environments/substitutions
----------------------------------------------

-- TODO: do we want to replace uses of this operation with something else?
env :: forall m v n. (SNatI m) => (Fin m -> v n) -> Env v m n
env f = fromVec v
  where
    v :: Vec m (v n)
    v = Vec.tabulate f

-- | The empty environment (zero domain)
zeroE :: Env v Z n
zeroE = Zero

-- | A singleton environment (single index domain)
-- maps that single variable to `v n`
oneE :: v n -> Env v (S Z) n
oneE v = Cons v zeroE

-- | an environment that maps index 0 to v and leaves
-- all other indices alone.
singletonE :: (SubstVar v) => v n -> Env v (S n) n
singletonE v = v .: idE

-- | identity environment, any size
idE :: (SubstVar v) => Env v n n
idE = Inc s0

-- | composition: do f then g
(.>>) :: (Subst v v) => Env v p n -> Env v n m -> Env v p m
f .>> g = comp f g

-- | `cons` -- extend an environment with a new mapping
-- for index '0'. All existing mappings are shifted over.
(.:) :: v m -> Env v n m -> Env v (S n) m
v .: f = Cons v f

-- | append two environments
-- The `SNatI` constraint is a runtime witness for the length
-- of the domain of the first environment. By using a class
-- constraint, this can be an infix operation.
(.++) ::
  (SNatI p, SubstVar v) =>
  Env v p n ->
  Env v m n ->
  Env v (p + m) n
(.++) = appendE snat

-- | append two environments: explicit length `SNat p` required
-- for the domain of the first list
appendE ::
  (SubstVar v) =>
  SNat p ->
  Env v p n ->
  Env v m n ->
  Env v (p + m) n
appendE SZ e1 e2 = e2
appendE (snat_ -> SS_ p1) e1 e2 = head e1 .: appendE p1 (tail e1) e2

newtype AppendE v m n p = MkAppendE
  { getAppendE ::
      Env v p n ->
      Env v m n ->
      Env v (p + m) n
  }

-- | inverse of `cons` -- remove the first mapping
tail :: (SubstVar v) => Env v (S n) m -> Env v n m
tail = comp (Inc s1)

-- | access value at index 0
head :: (SubstVar v) => Env v (S n) m -> v m
head f = applyEnv f FZ

-- | increment all free variables by 1
shift1E :: (SubstVar v) => Env v n (S n)
shift1E = Inc s1

-- | increment all free variables by m
shiftNE :: (SubstVar v) => SNat m -> Env v n (m + n)
shiftNE = Inc

-- make the bound bigger, but do not change any indices
-- this is an identity function
weakenE' :: forall m v n. SNat m -> Env v n (m + n)
weakenE' = Weak

-- make the bound bigger, on the right, but do not
-- change any indices.
-- this is an identity function
weakenER :: forall m v n. SNat m -> Env v n (n + m)
weakenER = WeakR

-- | modify an environment so that it can go under
-- a binder
up :: (SubstVar v) => Env v m n -> Env v (S m) (S n)
up (Inc SZ) = Inc SZ
up e = var Fin.f0 .: comp e (Inc s1)

-- | Shift an environment by size `p`
upN ::
  forall v p m n.
  (Subst v v) =>
  SNat p ->
  Env v m n ->
  Env v (p + m) (p + n)
upN p = getUpN @_ @_ @_ @p (withSNat p (induction base step))
  where
    base :: UpN v m n Z
    base = MkUpN id
    step :: forall p1. UpN v m n p1 -> UpN v m n (S p1)
    step (MkUpN r) = MkUpN $ \e -> var FZ .: comp (r e) (Inc s1)

newtype UpN v m n p = MkUpN {getUpN :: Env v m n -> Env v (p + m) (p + n)}

----------------------------------------------------
-- Create an environment from a length-indexed
-- vector of scoped values

fromVec :: Vec m (v n) -> Env v m n
fromVec VNil = zeroE
fromVec (x ::: vs) = x .: fromVec vs

-- toVec :: SNat m -> Env v m n -> Vec m (v n)
-- toVec SZ r = VNil
-- toVec (SS x) r = r x ::: toVec x (tail r)

----------------------------------------------------------------
-- Refinements
----------------------------------------------------------------

-- A refinement is a special kind of substitution that does not
-- change the scope, it just replaces all uses of a particular variable
-- with some other term (which could mention that variable).
newtype Refinement v n = Refinement (Map.Map (Fin n) (v n))

emptyR :: Refinement v n
emptyR = Refinement Map.empty

-- | Note, this operation fails when xs and ys have overlapping domains
joinR ::
  forall v n.
  (SNatI n, Subst v v, Eq (v n)) =>
  Refinement v n ->
  Refinement v n ->
  Maybe (Refinement v n)
joinR (Refinement xs) (Refinement ys) =
  Refinement <$> foldM f ys xs'
  where
    xs' = Map.toList xs
    r = fromTable xs'
    f :: Map.Map (Fin n) (v n) -> (Fin n, v n) -> Maybe (Map.Map (Fin n) (v n))
    f m (k, v)
      | Map.member k ys = Nothing
      | otherwise =
          let v' = applyE r v
           in Just $ if v' == var k then m else Map.insert k (applyE r v) m

singletonR :: (SubstVar v, Eq (v n)) => (Fin n, v n) -> Refinement v n
singletonR (x, t) =
  if t == var x then emptyR else Refinement (Map.singleton x t)

-- Move a refinement to a new scope
instance (Shiftable v) => Shiftable (Refinement v) where
  shift :: forall k n. SNat k -> Refinement v n -> Refinement v (k + n)
  shift k (Refinement (r :: Map.Map (Fin n) (v n))) = Refinement g'
    where
      f' = Map.mapKeysMonotonic (Fin.shiftN @k @n k) r
      g' = Map.map (shift k) f'

fromRefinement :: (SNatI n, SubstVar v) => Refinement v n -> Env v n n
fromRefinement (Refinement x) = fromTable (Map.toList x)

toRefinement :: (SNatI n, SubstVar v) => Env v n n -> Refinement v n
toRefinement r = Refinement (Map.fromList (tabulate r))

refines :: forall n v. (SNatI n, Subst v v, Eq (v n)) => Refinement v n -> Fin n -> Bool
refines r i = applyE (fromRefinement r) (var @v i) /= var @v i

refine :: (SNatI n, Subst v c) => Refinement v n -> c n -> c n
refine r = applyE (fromRefinement r)

domain :: Refinement v n -> [Fin n]
domain (Refinement m) = Map.keys m

----------------------------------------------------------------
-- show for environments
----------------------------------------------------------------

instance (SNatI n, Show (v m), SubstVar v) => Show (Env v n m) where
  show x = show (tabulate x)

tabulate :: (SNatI n, Subst v v) => Env v n m -> [(Fin n, v m)]
tabulate r = map (\f -> (f, applyEnv r f)) Fin.universe

fromTable ::
  forall n v.
  (SNatI n, SubstVar v) =>
  [(Fin n, v n)] ->
  Env v n n
fromTable rho =
  env $ \f -> case lookup f rho of
    Just t -> t
    Nothing -> var f

--------------------------------------------
-- Generic implementation of Subst class
-----------------------------------------------

newtype Ignore a = Ignore a

class GSubst v (e :: Nat -> Type) where
  gsubst :: Env v m n -> e m -> e n

-- Constant types
instance GSubst v (K1 i c) where
  gsubst s (K1 c) = K1 c
  {-# INLINE gsubst #-}

instance GSubst v U1 where
  gsubst _s U1 = U1
  {-# INLINE gsubst #-}

instance (GSubst b f) => GSubst b (M1 i c f) where
  gsubst s = M1 . gsubst s . unM1
  {-# INLINE gsubst #-}

instance GSubst b V1 where
  gsubst _s = error "BUG: void type"
  {-# INLINE gsubst #-}

instance (GSubst b f, GSubst b g) => GSubst b (f :*: g) where
  gsubst s (f :*: g) = gsubst s f :*: gsubst s g
  {-# INLINE gsubst #-}

instance (GSubst b f, GSubst b g) => GSubst b (f :+: g) where
  gsubst s (L1 f) = L1 $ gsubst s f
  gsubst s (R1 g) = R1 $ gsubst s g
  {-# INLINE gsubst #-}

instance (Subst b g) => GSubst b (Rec1 g) where
  gsubst s (Rec1 f) = Rec1 (applyE s f)

instance Shiftable Fin where
  shift = Fin.shiftN

instance (SubstVar v) => Subst v Fin where
  applyE r e = error "BUG: must use Fin type only for indices in syntax"

instance GSubst b Fin where
  gsubst s f = error "BUG: add a Var case to your definition of applyE"
