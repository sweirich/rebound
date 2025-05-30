{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Rebound.Env.Vector where

-- This is a lazy data structure: values stored in the vector are not forced
-- Uses Data.Vec to represent environments
-- Operations have more class constraints for the size of the vectors

import Rebound.Lib as Lib
import Data.Fin (Fin(..))
import qualified Data.Fin as Fin
import qualified Data.SNat as SNat
import Data.Vec (Vec(..))
import qualified Data.Vec as Vec
import GHC.Generics hiding (S)

------------------------------------------------------------------------------
-- Substitution class declarations
------------------------------------------------------------------------------
-- | Well-scoped types that can be the range of
-- an environment. This should generally be the `Var`
-- constructor from the syntax.
class (Subst v v) => SubstVar (v :: Nat -> Type) where
  var :: Fin n -> v n

-- | Apply the environment throughout a term of
-- type `c n`, replacing variables with values
-- of type `v m`
class (SubstVar v) => Subst v c where
  applyE :: Env v n m -> c n -> c m

  default applyE :: (Generic1 c, GSubst v (Rep1 c), SubstVar v) => Env v m n -> c m -> c n
  applyE = gapplyE
  {-# INLINE applyE #-}

-- Generic programming
class GSubst v (e :: Nat -> Type) where
  gsubst :: Env v m n -> e m -> e n

gapplyE :: (Generic1 c, GSubst v (Rep1 c), SubstVar v) => Env v m n -> c m -> c n
gapplyE = applyOpt (\s x -> to1 $ gsubst s (from1 x))
{-# INLINEABLE gapplyE #-}

applyOpt :: (Env v n m -> c n -> c m) -> (Env v n m -> c n -> c m)
applyOpt f = f

------------------------------------------------------------------------------
-- Environment representation
------------------------------------------------------------------------------
data Env (a :: Nat -> Type) (n :: Nat) (m :: Nat) = 
  SNatI m =>
  Env { 
    vec  :: !(Vec n (a m)), 
    size :: !(SNat n)
  }
  
withScope :: Env a n m -> ((SNatI n, SNatI m) => c) -> c
withScope (Env{size=sz}) x = withSNat sz x

applyEnv :: Env a n m -> Fin n -> a m
applyEnv e n = vec e Vec.! n
{-# INLINEABLE applyEnv #-}

-- | The empty environment (zero domain)
zeroE :: SNatI n => Env v Z n
zeroE = Env Vec.empty SZ
{-# INLINEABLE zeroE #-}

-- make the bound bigger, on the right, but do not change any indices. 
-- this is an identity function
weakenER :: forall m v n. (SNatI n, SubstVar v) => SNat m -> Env v n (n + m)
weakenER m = 
  withSNat (sPlus (snat @n) m)
  Env (Vec.tabulate (var . Fin.weakenFinRight m)) snat
{-# INLINEABLE weakenER #-}

-- make the bound bigger, on the left, but do not change any indices.
-- this is an identity function
weakenE' :: forall m v n. (SNatI n, SubstVar v) => SNat m -> Env v n (m + n)
weakenE' m = 
  withSNat (sPlus m (snat @n))
  Env (Vec.tabulate (var . Fin.weakenFin m)) snat
{-# INLINEABLE weakenE' #-}

-- | increment all free variables by m
shiftNE :: forall m n v. (SNatI n, SubstVar v) => SNat m -> Env v n (m + n)
shiftNE m = 
  withSNat (sPlus m (snat @n))
  Env (Vec.tabulate (var . Fin.shiftN m)) snat
{-# INLINEABLE shiftNE #-}

-- | `cons` -- extend an environment with a new mapping
-- for index '0'. All existing mappings are shifted over.
(.:) :: SNatI m => v m -> Env v n m -> Env v (S n) m
v .: f = 
  Env (v |> vec f) (SNat.ss (size f))
{-# INLINEABLE (.:) #-}

-- | composition: do f then g
(.>>) :: (Subst v v, SNatI m) => Env v p n -> Env v n m -> Env v p m
f .>> g = Env (fmap (applyE g) (vec f)) (size f)
{-# INLINEABLE (.>>) #-}

-- | inverse of `cons` -- remove the first mapping
tail :: Env v (S n) m -> Env v n m
tail (Env vs n) = Env vs' (SNat.prev n) where (_,vs') = Vec.unCons vs

-- | modify an environment so that it can go under
-- a binder
up :: (SubstVar v, SNatI m) => Env v n m -> Env v (S n) (S m)
up e = 
  withSNat (size e) $
     var Fin.f0 .: (e .>> shiftNE s1)
{-# INLINEABLE up #-}

-- | mapping operation for range of the environment
transform :: forall a b n m. (forall m. a m -> b m) -> Env a n m -> Env b n m
transform f e@(Env {}) = 
  Env { vec = fmap f (vec e) , size = (size e)} where
