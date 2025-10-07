-- |
-- Module: Rebound.Refinement
-- Description : Refinement from variables to terms
--
-- Refinements map variables in a scope to terms which live in the same scope.

module Rebound.Refinement(
    Refinement(..),
    emptyR,
    joinR,
    singletonR,
    toEnvironment,
    fromEnvironment,
    refine,
    domain)
 where

import Rebound.Lib ( SNatI, SNat, type (+), Fin )
import Rebound.Env
import Data.Map as Map
import Control.Monad
import Data.Fin as Fin

-- | A refinement is a special kind of substitution that does not
-- change the scope, it just replaces all uses of a particular variable
-- with some other term, which lives in the same scope.
newtype Refinement v n = Refinement (Map (Fin n) (v n))

-- | The empty refinement. Maps every variable to itself.
emptyR :: Refinement v n
emptyR = Refinement Map.empty

-- | Join/merge/meld two refinements.
-- Fails if the two refinements have overlapping domains.
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

-- | A singleton refinement.
-- Maps the specified variable to the specified term, and every other variable
-- gets mapped to itself.
singletonR :: (SubstVar v, Eq (v n)) => (Fin n, v n) -> Refinement v n
singletonR (x, t) =
  if t == var x then emptyR else Refinement (Map.singleton x t)

instance (Shiftable v) => Shiftable (Refinement v) where
  shift :: forall k n. SNat k -> Refinement v n -> Refinement v (k + n)
  shift k (Refinement (r :: Map.Map (Fin n) (v n))) = Refinement g'
    where
      f' = Map.mapKeysMonotonic (Fin.shiftN @k @n k) r
      g' = Map.map (shift k) f'

-- | Convert a refinement into an environment.
toEnvironment :: (SNatI n, SubstVar v) => Refinement v n -> Env v n n
toEnvironment (Refinement x) = fromTable (Map.toList x)

-- | Convert a refinement to an environment.
fromEnvironment :: (SNatI n, SubstVar v) => Env v n n -> Refinement v n
fromEnvironment r = Refinement (Map.fromList (tabulate r))

-- | Checks whether this refinement refines a variable.
refines :: forall n v. (SNatI n, Subst v v, Eq (v n)) => Refinement v n -> Fin n -> Bool
refines r i = applyE (toEnvironment r) (var @v i) /= var @v i

-- | Apply the refinement to a variable.
refine :: (SNatI n, Subst v c) => Refinement v n -> c n -> c n
refine r = applyE (toEnvironment r)

-- | Returns the domain of the environment (i.e., the list of refined variables).
domain :: Refinement v n -> [Fin n]
domain (Refinement m) = Map.keys m