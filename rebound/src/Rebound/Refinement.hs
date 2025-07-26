module Rebound.Refinement(
    Refinement(..),
    emptyR,
    joinR,
    singletonR,
    fromRefinement,
    toRefinement,
    refine,
    domain)
 where

import Rebound.Lib ( SNatI, SNat, type (+), Fin )
import Rebound.Env
import Data.Map as Map
import Control.Monad
import Data.Fin as Fin

-- A refinement is a special kind of substitution that does not
-- change the scope, it just replaces all uses of a particular variable
-- with some other term (which could mention that variable).
newtype Refinement v n = Refinement (Map (Fin n) (v n))

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