-- |
-- Module      : Rebound.Env
-- Description : Environments
-- Stability   : experimental
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ViewPatterns #-}
module Rebound.Env(Env, applyEnv, 
  SubstVar(..), Subst(..), 
  GSubst(..), gapplyE, applyOpt,
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
  Refinement(..),
  emptyR,
  joinR,
  singletonR,
  fromRefinement,
  toRefinement,
  shiftRefinement,
  refine,
  tabulate,
  fromTable,
  weakenE',
  weakenER,
  withScope
  ) where

import Rebound.Lib
import Prelude hiding (head,tail)   
import qualified Data.Vec as Vec
import qualified Data.Map as Map
import Control.Monad
import GHC.Generics hiding (S)
import Data.Fin (Fin(..))
import qualified Data.Fin as Fin
import qualified Data.SNat as SNat

import Rebound.Env.Internal

----------------------------------------------
-- operations on environments/substitutions
----------------------------------------------

-- TODO: do we want to replace uses of this operation with something else?
env :: forall m v n. (SubstVar v, SNatI m, SNatI n) => (Fin m -> v n) -> Env v m n
env f = fromVec v where
        v :: Vec m (v n)
        v = Vec.tabulate f
  

-- | A singleton environment (single index domain)
-- maps that single variable to `v n`
oneE :: (SubstVar v, SNatI n) => v n -> Env v (S Z) n
oneE v = v .: zeroE

-- | an environment that maps index 0 to v and leaves
-- all other indices alone.
singletonE :: (SubstVar v, SNatI n) => v n -> Env v (S n) n
singletonE v = v .: idE
 
-- | identity environment, any size
idE :: (SubstVar v, SNatI n) => Env v n n
idE = shiftNE s0

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
appendE p = getAppendE (withSNat p (induction base step)) where
  base = MkAppendE $ \e1 e2 -> e2
  step :: SubstVar v => AppendE v m n p -> AppendE v m n (S p)
  step (MkAppendE r) = MkAppendE $ \e1 e2 -> 
    withScope e1 $
       head e1 .: r (tail e1) e2

newtype AppendE v m n p =
     MkAppendE { getAppendE :: 
       Env v p n ->
       Env v m n ->
       Env v (p + m) n }

-- | access value at index 0
head :: (SubstVar v) => Env v (S n) m -> v m
head f = applyEnv f f0

-- | increment all free variables by 1
shift1E :: (SubstVar v, SNatI n) => Env v n (S n)
shift1E = shiftNE s1

-- | Shift an environment by size `p`
upN :: forall v p m n.
  (Subst v v, SNatI n) =>
  SNat p ->
  Env v m n ->
  Env v (p + m) (p + n)
upN p = getUpN @_ @_ @_ @p (withSNat p (induction base step)) p where
   base :: UpN v m n Z
   base = MkUpN (const id)
   step :: forall p1. UpN v m n p1 -> UpN v m n (S p1)
   step (MkUpN r) = MkUpN 
    $ \p e -> withSNat (sPlus (SNat.prev p) (snat @n)) $ var Fin.f0 .: (r (SNat.prev p) e .>> shiftNE s1)

newtype UpN v m n p = 
    MkUpN { getUpN :: SNat p -> Env v m n -> Env v (p + m) (p + n) }

----------------------------------------------------
-- Create an environment from a length-indexed 
-- vector of scoped values

fromVec :: (SubstVar v, SNatI n) => Vec m (v n) -> Env v m n
fromVec v = getEnv (Vec.induction v base step) where
  base :: SNatI n => EnvN v n Z
  base = EnvN zeroE
  step :: (SubstVar v, SNatI n) => v n -> EnvN v n m -> EnvN v n (S m)
  step x (EnvN r) = EnvN (x .: r)


newtype EnvN v n m = EnvN { getEnv :: Env v m n } 


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
joinR :: forall v n. (SNatI n, Subst v v, Eq (v n)) => 
   Refinement v n -> Refinement v n -> Maybe (Refinement v n)
joinR (Refinement xs) (Refinement ys) = 
  Refinement <$> foldM f ys xs' where
     xs' = Map.toList xs
     r = fromTable xs'
     f :: Map.Map (Fin n) (v n) -> (Fin n, v n) -> Maybe (Map.Map (Fin n) (v n))
     f m (k,v) | Map.member k ys = Nothing
               | otherwise = 
                  let v' = applyE r v in
                  Just $ if v' == var k then m else Map.insert k (applyE r v) m
  

singletonR :: (SubstVar v, Eq (v n)) => (Fin n,v n) -> Refinement v n
singletonR (x, t) = 
  if t == var x then emptyR else Refinement (Map.singleton x t)


-- Move a refinement to a new scope
shiftRefinement :: forall p n v. (SubstVar v, SNatI n) => SNat p -> Refinement v n -> Refinement v (p + n)
shiftRefinement p (Refinement (r :: Map.Map (Fin n) (v n))) = Refinement g' where
  f' = Map.mapKeysMonotonic (Fin.shiftN @p @n p) r
  g' = Map.map (applyE @v (shiftNE p)) f'


fromRefinement :: (SNatI n, SubstVar v) => Refinement v n -> Env v n n
fromRefinement (Refinement x) = fromTable (Map.toList x)

toRefinement :: (SNatI n, SubstVar v) => Env v n n -> Refinement v n
toRefinement r = Refinement (Map.fromList (tabulate r))

refine :: (SNatI n, Subst v c) => Refinement v n -> c n -> c n
refine r = applyE (fromRefinement r)

----------------------------------------------------------------
-- show for environments
----------------------------------------------------------------

instance (SNatI n, Show (v m), SubstVar v) => Show (Env v n m) where
  show x = show (tabulate x)

tabulate :: (SNatI n, Subst v v) => Env v n m -> [(Fin n, v m)]
tabulate r = map (\f -> (f, applyEnv r f)) Fin.universe

fromTable :: forall n v. (SNatI n, SubstVar v) => 
  [(Fin n, v n)] -> Env v n n
fromTable rho = 
  env $ \f -> case lookup f rho of 
                Just t -> t 
                Nothing -> var f
                                  
--------------------------------------------
-- Generic implementation of Subst class
-----------------------------------------------

-- Constant types
instance GSubst v (K1 i c) where
  gsubst s (K1 c) = K1 c
  {-# INLINE gsubst #-}

instance GSubst v U1 where
  gsubst _s U1 = U1
  {-# INLINE gsubst #-}

instance GSubst b f => GSubst b (M1 i c f) where
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

instance SubstVar Fin where
  var x = x

instance {-# OVERLAPS #-} Subst Fin Fin where
  applyE = applyEnv

instance {-# OVERLAPPABLE #-} SubstVar v => Subst v Fin where
  applyE = error "BUG: this case is impossible"


instance GSubst b Fin where
  gsubst s f = error "BUG: add a Var case to your definition of applyE"

