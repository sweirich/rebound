{-|
Module      : AutoEnv
Description : Explicit substitutions
Stability   : experimental


-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module AutoEnv where

import Prelude hiding (head,tail)
import Data.Type.Equality

import Lib
import Data.Kind
import qualified Data.List as List
import Vec (Vec(..))
import qualified Vec

-- | An environment (or explicit substitution) that map
-- indices bounded by `m`, to values of type `v n`
-- For now, we represent this directly as a function, 
-- but we might want to change that. So we wrap it in 
-- a newtype to hide the representation.
newtype Env v m n = Env { applyEnv :: Fin m -> v n }

-- | Well-scoped types that can be the range of 
-- an environment. This should generally be the `Var`
-- constructor from the syntax.
class SubstVar (v :: Nat -> Type) where
    var    :: Fin n -> v n

-- | Apply the environment throughout a term of 
-- type `c n`, replacing variables with values 
-- of type `v m`
class SubstVar v => Subst v c where
    applyE :: Env v n m -> c n -> c m


----------------------------------------------
-- operations on environments/substitutions
----------------------------------------------

-- | The empty environment (zero domain)
zeroE :: Env v Z n
zeroE = Env $ \case

-- | A singleton environment (single index domain)
-- maps that single variable to `v n`
oneE :: v n -> Env v (S Z) n
oneE v = Env $ const v

-- | an environment that maps index 0 to v and leaves 
-- all other indices alone. Unlike oneE above, the 
-- domain of the environment must match the number of 
-- variables in the range.
singleton :: SubstVar v => v n -> Env v n n
singleton v = Env $ \ case FZ -> v ; FS y -> var (FS y)

-- | identity environment, any size
idE :: SubstVar v => Env v n n
idE = Env var

-- | composition: do f then g
(.>>) :: Subst v v => Env v p n -> Env v n m -> Env v p m
f .>> g = Env $ applyE g . applyEnv f

-- | `cons` -- extend an environment with a new mapping 
-- for index '0'. All existing mappings are shifted over.
(.:) :: SubstVar v => v m -> Env v n m -> Env v (S n) m
v .: f = Env $ \ case FZ -> v ; (FS x) -> applyEnv f x 

-- | append two environments
-- The `SNatI` constraint is a runtime witness for the length
-- of the domain of the first environment. By using a class
-- constraint, this can be an infix operation. 
(.++) :: (SNatI p, SubstVar v) => 
    Env v p n -> Env v m n -> Env v (Plus p m) n
(.++) = appendE snat
    
-- | append two environments: explicit length `SNat p` required
-- for the domain of the first list
appendE :: SubstVar v =>
        SNat p -> Env v p n -> Env v m n -> Env v (Plus p m) n
appendE SZ e1 e2 = e2 
appendE (SS p1) e1 e2 = head e1 .: appendE p1 (tail e1) e2
      
-- | inverse of `cons` -- remove the first mapping
tail :: SubstVar v => Env v (S n) m -> Env v n m
tail f = Env (applyEnv f . FS )

-- | access value at index 0
head :: SubstVar v => Env v (S n) m -> v m
head f = applyEnv f FZ

-- | increment all free variables by 1
shift :: SubstVar v => Env v n (S n)
shift = Env (var . FS)

-- | weaken variables by 1
-- makes their bound bigger but does not change any of their indices
weakenOneE :: SubstVar v => Env v n (S n)
weakenOneE = Env (var . weaken1Fin)

weakenE' :: forall m v n. (SubstVar v) => SNat m -> Env v n (Plus m n)
weakenE' sm = Env (var . weakenFin sm)

----------------------------------------------------------------
-- Single binders
----------------------------------------------------------------
-- | Type for a single binders
-- includes an delayed substitution plus a term with an 
-- extra free variable for the binder
-- n is the number of free variables in the term
data Bind v c (n :: Nat) where
    Bind :: Env v m n -> c (S m) -> Bind v c n

-- | The substitution operation composes the explicit 
-- substitution with the one stored at the binder
instance Subst v v => Subst v (Bind v c) where
    applyE :: Subst v v => Env v n m -> Bind v c n -> Bind v c m
    applyE env1 (Bind env2 m) = Bind (env2 .>> env1) m

-- | create a single binder
bind :: Subst v c => c (S n) -> Bind v c n
bind = Bind idE

-- | instantiate a binder with a term
instantiate :: (Subst v c) => Bind v c n -> v n -> c n
instantiate b v = unbindWith (\ r e -> applyE (v .: r) e) b

-- | apply an environment-parameterized function while
-- instantiating
instantiateWith :: (SubstVar v) =>
         (forall m n. Env v m n -> c m -> c n) ->
         Bind v c n -> v n -> c n
instantiateWith f b v = unbindWith (\ r e -> f ( v .: r) e) b


-- | modify an environment so that it can go under 
-- a binder
up :: Subst v v => Env v m n -> Env v (S m) (S n)
up e = var FZ .: (e .>> shift)

-- | access the body of the binder  (inverse of bind)
unbind :: forall v c n. (Subst v v, Subst v c) => Bind v c n -> c (S n)
unbind (Bind r t) = applyE (up r) t

-- | unbind a binder and apply the function to the argument and subterm
unbindWith :: (SubstVar v) => 
    (forall m. Env v m n -> c (S m) -> d) ->
    Bind v c n -> d
unbindWith f (Bind r t) = f r t

-- | apply an environment-parameterized function & environment 
-- underneath a binder
applyUnder :: (Subst v v, Subst v c) =>
        (forall m n. Env v m n -> c m -> c n) -> Env v n1 n2 ->
        Bind v c n1 -> Bind v c n2
applyUnder f r2 (Bind r1 t) = 
    bind (f (up (r1 .>> r2)) t)

-- TODO: this implementation of strengthening for binders is rather inefficient
-- maybe there is a better way to do it???
instance (SubstVar v, Subst v v, Subst v c, Strengthen c) => Strengthen (Bind v c) where
    strengthen' (m :: SNat m) (n :: SNat n) b = 
        case axiom @m @n of
          Refl -> bind <$> strengthen' m (SS n) (unbind b)

----------------------------------------------------------
-- Pattern binding (N-ary binding)
----------------------------------------------------------

-- | A pattern is any type that can be made an instance of the 
-- `Sized` type class. 
-- The `PatBind` type generalizes the definitions above 
-- to bind (Size p) variables. 
-- As in `Bind` above, this type includes a delayed substitution
-- for the variables in the body of the binder.
data PatBind v c (p :: Type) (n :: Nat) where
    PatBind :: p -> Env v m n -> c (Plus (Size p) m) 
            -> PatBind v c p n

-- | Create a `PatBind` with an identity substitution.
patBind :: (Sized p, Subst v c) => p -> c (Plus (Size p) n) -> PatBind v c p n
patBind pat = PatBind pat idE

-- | Access the pattern of a pattern binding
getPat :: PatBind v c p n -> p
getPat (PatBind pat env t) = pat

-- | Access the body of a pattern binding.
-- The pattern type determines the number of variables
-- bound in the pattern
unPatBind :: 
    (Sized p, Subst v v, Subst v c) => PatBind v c p n 
    -> c (Plus (Size p) n)
unPatBind (PatBind pat env t) = 
    applyE (upN (size pat) env) t

-- | Shift an environment by size `p` 
upN :: (Subst v v) => 
        SNat p -> Env v m n -> Env v (Plus p m) (Plus p n)
upN SZ = id
upN (SS n) = \ e -> var FZ .: (upN n e .>> shift)

-- | Apply a function to the pattern, suspended environment and body
-- in a pattern binding
unPatBindWith ::  (Sized p, SubstVar v) => 
    (forall m. p -> Env v m n -> c (Plus (Size p) m) -> d) -> PatBind v c p n -> d
unPatBindWith f (PatBind pat r t) = f pat r t

instantiatePat :: forall v c p n. (Sized p, Subst v c) => 
   PatBind v c p n -> Env v (Size p) n -> c n
instantiatePat b e = unPatBindWith 
    (\ p r t -> withSNat (size p) $ applyE (e .++ r) t) b

applyPatUnder :: (Sized p, Subst v v, Subst v c) => 
   (forall m n. Env v m n -> c m -> c n) -> Env v n1 n2 ->
        PatBind v c p n1 -> PatBind v c p n2
applyPatUnder f r2 (PatBind p r1 t) = 
    patBind p (f (upN (size p) (r1 .>> r2)) t)

instantiatePatWith :: (Sized p, SubstVar v) =>
         (forall m n. Env v m n -> c m -> c n) ->
         PatBind v c p n -> Env v (Size p) n -> c n
instantiatePatWith f b v = 
    unPatBindWith (\ p r e -> withSNat (size p) $ f (v .++ r) e) b

instance Subst v v => Subst v (PatBind v c p) where
    applyE env1 (PatBind p env2 m) = 
        PatBind p (env2 .>> env1) m

instance (Sized p, SubstVar v, Subst v v, Subst v c, Strengthen c) => Strengthen (PatBind v c p) where

    strengthen' (m :: SNat m) (n :: SNat n) b = 
        case axiomM @m @(Size p) @n of
          Refl -> patBind (getPat b) <$> strengthen' m (sPlus (size (getPat b)) n) (unPatBind b)

----------------------------------------------------------------
-- Double binder
----------------------------------------------------------------

-- A double binder is isomorphic to a pattern binding with 
-- "SNat 2" as the pattern.

type Bind2 v c n = PatBind v c (SNat N2) n

bind2 :: Subst v c => c (S (S n)) -> Bind2 v c n
bind2 = patBind s2

unbind2 :: forall v c n. (Subst v v, Subst v c) => Bind2 v c n -> c (S (S n))
unbind2 = unPatBind

unbind2With :: (SubstVar v) => 
    (forall m. Env v m n -> c (S (S m)) -> d) ->
    Bind2 v c n -> d
unbind2With f = 
    unPatBindWith (const f)

instantiate2 :: (Subst v c) => Bind2 v c n -> v n -> v n -> c n
instantiate2 b v1 v2 = instantiatePat b (v1 .: (v2 .: zeroE))

{-
data Bind2 v c (n :: Nat) where
    Bind2 :: Env v m n -> c (S (S m)) -> Bind2 v c n

bind2 :: Subst v c => c (S (S n)) -> Bind2 v c n
bind2 = Bind2 (Env var)

instance Subst v v => Subst v (Bind2 v c) where
    applyE :: SubstVar v => Env v n m -> Bind2 v c n -> Bind2 v c m
    applyE env1 (Bind2 env2 m) = Bind2 (env2 .>> env1) m

-- | access the body of the binder  (inverse of bind)
unbind2 :: forall v c n. (Subst v v, Subst v c) => Bind2 v c n -> c (S (S n))
unbind2 (Bind2 env t) = applyE (up (up env)) t

-- | unbind a binder and apply the function to the argument and subterm.
unbind2With :: (SubstVar v) => 
    (forall m. Env v m n -> c (S (S m)) -> d) ->
    Bind2 v c n -> d
unbind2With f (Bind2 r t) = f r t

-- | instantiate a binder with a term
instantiate2 :: forall v c n. (Subst v c) => Bind2 v c n -> v n -> v n -> c n
instantiate2 b v1 v2 = unbind2With (\ r e -> applyE (v1 .: (v2 .: r)) e) b
-}
----------------------------------------------------------------
-- For dependently-typed languages

-- This is not weakening --- it increments all variables by one
shiftC :: forall v c n. Subst v c => c n -> c (S n)
shiftC = applyE @v shift

type Ctx v n = Env v n n

shiftCtx :: Subst v v => Env v n n -> Env v n (S n)
shiftCtx g = g .>> shift

(+++) :: forall v n. Subst v v => Ctx v n -> v n -> Ctx v (S n)
g +++ a = shiftC @v @v a .: shiftCtx g 

----------------------------------------------------------------
toList :: SNatI n => Env v n m -> [v m]
toList r = map (applyEnv r) (enumFin snat)

instance (SNatI n, Show (v m)) => Show (Env v n m) where
    show x = show (toList x)
