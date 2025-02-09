-- |
-- Module      : AutoEnv.Env
-- Description : Environments
-- Stability   : experimental
{-# LANGUAGE UndecidableSuperClasses #-}
module AutoEnv.Env(Env, applyEnv, SubstVar(..), Subst(..),
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
  weakenER
  ) where

import AutoEnv.Lib
--import AutoEnv.Classes
import Prelude hiding (head,tail)   
import qualified Data.Vec as Vec
import qualified Data.Map as Map
import Control.Monad

-- type Env a n m = Fin n -> a m

data Env (a :: Nat -> Type) (n :: Nat) (m :: Nat) where
  Zero  :: Env a Z n
  WeakR :: !(SNat m) -> Env a n (Plus n m) --  weaken values in range by m
  Weak  :: !(SNat m) -> Env a n (Plus m n) --  weaken values in range by m
  Inc   :: !(SNat m) -> Env a n (Plus m n) --  increment values in range (shift) by m
  Cons  :: (a m) -> !(Env a n m) -> Env a ('S n) m --  extend a substitution (like cons)
  (:<>) :: !(Env a m n) -> !(Env a n p) -> Env a m p --  compose substitutions

--  Value of the index x in the substitution s
applyEnv :: SubstVar a => Env a n m -> Fin n -> a m
applyEnv Zero x = case x of {}
applyEnv (Inc m) x = var (shiftN m x)
applyEnv (WeakR m) x = var (weakenFinRight m x)
applyEnv (Weak m) x = var (weakenFin m x)
applyEnv (Cons ty _s) FZ = ty
applyEnv (Cons _ty s) (FS x) = applyEnv s x
applyEnv (s1 :<> s2) x = applyE s2 (applyEnv s1 x)
{-# INLINEABLE applyEnv #-}

-- | smart constructor for composition
comp :: forall a m n p. SubstVar a => Env a m n -> Env a n p -> Env a m p
comp Zero s = Zero
comp (Weak (k1 :: SNat m1)) (Weak (k2 :: SNat m2))  = 
  case axiomAssoc @m2 @m1 @m of
    Refl -> Weak (sPlus k2 k1)
comp (Weak SZ) s = s
comp s (Weak SZ) = s
comp (Inc (k1 :: SNat m1)) (Inc (k2 :: SNat m2))  = 
  case axiomAssoc @m2 @m1 @m of
    Refl -> Inc (sPlus k2 k1)
comp (Inc SZ) s = s
comp s (Inc SZ) = s
comp (Inc (SS n)) (Cons _t s) = comp (Inc n) s
comp (s1 :<> s2) s3 = comp s1 (comp s2 s3)
comp (Cons t s1) s2 = Cons (applyE s2 t) (comp s1 s2)
comp s1 s2 = s1 :<> s2
{-# INLINEABLE comp #-}

-- | mapping operation for range
-- TODO: look up conor's name
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

-- | Apply the environment throughout a term of
-- type `c n`, replacing variables with values
-- of type `v m`
class (SubstVar v) => Subst v c where
  applyE :: Env v n m -> c n -> c m

----------------------------------------------
-- operations on environments/substitutions
----------------------------------------------

-- TODO: do we want to replace uses of this operation with something else?
env :: forall m v n. SNatI m => (Fin m -> v n) -> Env v m n
env f = fromVec v where
        v :: Vec m (v n)
        v = Vec.tabulate (snat @m) f
  

-- | The empty environment (zero domain)
zeroE :: Env v Z n
zeroE = Zero

-- | A singleton environment (single index domain)
-- maps that single variable to `v n`
oneE :: v n -> Env v (S Z) n
oneE v = Cons v zeroE

singletonE :: (SubstVar v) => v n -> Env v (S n) n
singletonE v = v .: idE

-- | an environment that maps index 0 to v and leaves
-- all other indices alone. Unlike oneE above, the
-- domain of the environment must match the number of
-- variables in the range.
-- singleton :: (SubstVar v) => v n -> Env v n n
-- singleton v = v .: idE

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
tail = comp (Inc s1)

-- | access value at index 0
head :: (SubstVar v) => Env v (S n) m -> v m
head f = applyEnv f FZ

-- | increment all free variables by 1
shift1E :: (SubstVar v) => Env v n (S n)
shift1E = Inc s1

-- | increment all free variables by m
shiftNE :: (SubstVar v) => SNat m -> Env v n (Plus m n)
shiftNE = Inc

{-
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
-}

{-
-- | weaken variables by 1
-- makes their bound bigger but does not change any of their indices
weakenOneE :: (SubstVar v) => Env v n (S n)
weakenOneE = Env (var . weaken1Fin)
-}

-- make the bound bigger, but do not change any indices
weakenE' :: forall m v n. SNat m -> Env v n (Plus m n)
weakenE' = Weak
  -- Env (var . weakenFin sm)

weakenER :: forall m v n. SNat m -> Env v n (Plus n m)
weakenER = WeakR 

-- | modify an environment so that it can go under
-- a binder
up :: (Subst v v) => Env v m n -> Env v (S m) (S n)
up e = var f0 .: comp e (Inc s1)

-- | Shift an environment by size `p`
upN ::
  (Subst v v) =>
  SNat p ->
  Env v m n ->
  Env v (Plus p m) (Plus p n)
upN SZ = id
upN (SS n) = \e -> var FZ .: comp (upN n e) (Inc s1)

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
shiftRefinement :: forall p n v. (Subst v v) => SNat p -> Refinement v n -> Refinement v (Plus p n)
shiftRefinement p (Refinement (r :: Map.Map (Fin n) (v n))) = Refinement g' where
  f' = Map.mapKeysMonotonic (shiftN @p @n p) r
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
tabulate r = map (\f -> (f, applyEnv r f)) (enumFin snat)

fromTable :: forall n v. (SNatI n, SubstVar v) => 
  [(Fin n, v n)] -> Env v n n
fromTable rho = 
  env $ \f -> case lookup f rho of 
                Just t -> t 
                Nothing -> var f
                                    