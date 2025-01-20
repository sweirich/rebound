module AutoEnv.Env(Env,
  zeroE,
  oneE,
  singleton,
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
  weakenE'
  ) where

import AutoEnv.Lib
import AutoEnv.Classes
import Prelude hiding (head,tail)   
import qualified Data.Map as Map
import Control.Monad

----------------------------------------------
-- operations on environments/substitutions
----------------------------------------------

-- | The empty environment (zero domain)
zeroE :: Env v Z n
zeroE = Env $ \case {}

-- | A singleton environment (single index domain)
-- maps that single variable to `v n`
oneE :: v n -> Env v (S Z) n
oneE v = Env $ const v

-- | an environment that maps index 0 to v and leaves
-- all other indices alone. Unlike oneE above, the
-- domain of the environment must match the number of
-- variables in the range.
singleton :: (SubstVar v) => v n -> Env v n n
singleton v = Env $ \case FZ -> v; FS y -> var (FS y)

-- | identity environment, any size
idE :: (SubstVar v) => Env v n n
idE = Env var

-- | composition: do f then g
(.>>) :: (Subst v v) => Env v p n -> Env v n m -> Env v p m
f .>> g = Env $ applyE g . applyEnv f

-- | `cons` -- extend an environment with a new mapping
-- for index '0'. All existing mappings are shifted over.
(.:) :: v m -> Env v n m -> Env v (S n) m
v .: f = Env $ \case FZ -> v; (FS x) -> applyEnv f x

-- | append two environments
-- The `SNatI` constraint is a runtime witness for the length
-- of the domain of the first environment. By using a class
-- constraint, this can be an infix operation.
(.++) ::
  (SNatI p, SubstVar v) =>
  Env v p n ->
  Env v m n ->
  Env v (Plus p m) n
(.++) = appendE snat

-- | append two environments: explicit length `SNat p` required
-- for the domain of the first list
appendE ::
  (SubstVar v) =>
  SNat p ->
  Env v p n ->
  Env v m n ->
  Env v (Plus p m) n
appendE SZ e1 e2 = e2
appendE (SS p1) e1 e2 = head e1 .: appendE p1 (tail e1) e2

-- | inverse of `cons` -- remove the first mapping
tail :: (SubstVar v) => Env v (S n) m -> Env v n m
tail f = Env (applyEnv f . FS)

-- | access value at index 0
head :: (SubstVar v) => Env v (S n) m -> v m
head f = applyEnv f FZ

-- | increment all free variables by 1
shift1E :: (SubstVar v) => Env v n (S n)
shift1E = Env (var . FS)

-- | increment all free variables by m
shiftNE :: (SubstVar v) => SNat m -> Env v n (Plus m n)
shiftNE m = Env (var . shiftN m)

-- | increment all free variables by m, but in the middle
shiftRE ::
  forall v n1 n2 n.
  (SubstVar v) =>
  SNat n2 ->
  Env v (Plus n1 n) (Plus (Plus n1 n2) n)
shiftRE n2 = Env (var . shiftR @n1 @n2 @n n2)

-- | increment all free variables by m, but at the top
shiftLE ::
  forall v n1 n2 n.
  (SubstVar v) =>
  SNat n1 ->
  Env v (Plus n2 n) (Plus (Plus n1 n2) n)
shiftLE n1 = Env (var . shiftL @n1 @n2 @n n1)

-- | weaken variables by 1
-- makes their bound bigger but does not change any of their indices
weakenOneE :: (SubstVar v) => Env v n (S n)
weakenOneE = Env (var . weaken1Fin)

weakenE' :: forall m v n. (SubstVar v) => SNat m -> Env v n (Plus m n)
weakenE' sm = Env (var . weakenFin sm)

-- | modify an environment so that it can go under
-- a binder
up :: (Subst v v) => Env v m n -> Env v (S m) (S n)
up e = var FZ .: (e .>> shift1E)

-- | Shift an environment by size `p`
upN ::
  (Subst v v) =>
  SNat p ->
  Env v m n ->
  Env v (Plus p m) (Plus p n)
upN SZ = id
upN (SS n) = \e -> var FZ .: (upN n e .>> shift1E)

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
joinR :: forall v n. (Subst v v, Eq (v n)) => Refinement v n -> Refinement v n -> Maybe (Refinement v n)
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
shiftRefinement :: forall p n v. (Subst v v) => SNat p -> Refinement v n -> Refinement v (Plus p n)
shiftRefinement p (Refinement (r :: Map.Map (Fin n) (v n))) = Refinement g' where
  f' = Map.mapKeysMonotonic (shiftN @p @n p) r
  g' = Map.map (applyE @v (shiftNE p)) f'


fromRefinement :: SubstVar v => Refinement v n -> Env v n n
fromRefinement (Refinement x) = fromTable (Map.toList x)

toRefinement :: SNatI n => Env v n n -> Refinement v n
toRefinement r = Refinement (Map.fromList (tabulate r))

refine :: (Subst v c) => Refinement v n -> c n -> c n
refine r = applyE (fromRefinement r)

----------------------------------------------------------------
-- show for environments
----------------------------------------------------------------

instance (SNatI n, Show (v m)) => Show (Env v n m) where
  show x = show (tabulate x)

tabulate :: (SNatI n) => Env v n m -> [(Fin n, v m)]
tabulate r = map (\f -> (f, applyEnv r f)) (enumFin snat)

fromTable :: SubstVar v => [(Fin n, v n)] -> Env v n n
fromTable rho = Env $ \f -> case lookup f rho of 
                                    Just t -> t 
                                    Nothing -> var f