-- This is an example that does not use the rebound library
-- instead it adapts the structure of rebound to the "names for free" 
-- technique of Bernardy and Pouillard.

{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

module FreeBound where

import Data.Kind (Type)
import Prelude hiding (pi)

-------------------------------------------------------------------
-- scopes, variables, and binding

type Tag = Type -- a type for parametric names, needs to be extensible

-- The name type: indexed by a tag so that we can distinguish different names
-- NB: This type is isomorphic to unit.
data Name (a :: Tag) = Name

-- a scope is a snoc list of tags each where tag is 
-- a static "name" for a variable currently in scope. 
data Scope where
   Nil  :: Scope
   (:>) :: Scope -> Tag -> Scope 

-- de Bruijn indices represent variables in a scope
-- this type is isomorphic to "Fin" but the index is a list of tags
-- instead of a single nat
data Index (s :: Scope) where
    I0 :: Index (s :> a)
    IS :: Index s -> Index (s :> a)

-- we can turn them into numbers for printing
toInt :: Index s -> Int
toInt I0 = 0
toInt (IS x) = 1 + toInt x

instance Show (Index s) where show i = show (toInt i) 


---------------------------------------------------------------------
-- type classes for indices

-- | membership in scope
-- If a variable is in scope, then we should be able to get its 
-- index in that scope
class (a :: Tag) ∈ (s :: Scope) where
    inj :: Name a -> Index s

-- type class magic to calculate the index
instance {-# OVERLAPPING #-} a ∈ (s :> a) where 
    inj _ = I0
instance {-# INCOHERENT #-} (a ∈ n) => a ∈ (n :> b)
    where inj p = IS (inj p) 

-- | scope inclusion, witnessed by a substitution (see below)
-- this should be a renaming (Index s -> Index s'), but we 
-- are being a little lazy here
class (s :: Scope) ⊆ (s' :: Scope) where
    incl :: Sub Exp s s'

instance {-# OVERLAPPING #-} n ⊆ n where incl = idE
instance {-# INCOHERENT #-} (m ⊆ n) => m ⊆ (n :> a) 
    where incl = incl .>> shift
instance {-# INCOHERENT #-} (m ⊆ n) => ((m :> a) ⊆ (n :> a))
    where incl = up incl


--------------------------------------------------------------------
-- Substitutions as closures
-- this code is the same as in rebound, except that it uses Index 
-- instead of Fin

type Sub v (s1 :: Scope) (s2 :: Scope) = Index s1 -> v s2

-- class of types that have a var constructor
class (Subst v v) => SubstVar v where
    ivar :: Index m -> v m

-- class of types that we can apply substitutions to
class SubstVar v => Subst v c where
    applyE :: Sub v m n -> c m -> c n

zero :: Sub v Nil s
zero = \x -> case x of {}

idE :: SubstVar v => Sub v n n 
idE = ivar

shift :: SubstVar v => Sub v m (m :> a)
shift = ivar . IS

(.>>) :: Subst v v => Sub v s1 s2 -> Sub v s2 s3 -> Sub v s1 s3 
r1 .>> r2 = applyE r2 . r1

(.:) :: SubstVar v => v m -> Sub v n m -> Sub v (n :> a) m
ty .: s = \y -> case y of 
                    I0 -> ty
                    IS x -> s x

up :: Subst v v => Sub v s1 s2 -> Sub v (s1 :> a) (s2 :> a)
up rho = ivar I0 .: skip rho

skip :: Subst v v => Sub v m n -> Sub v m (n :> a)
skip e = e .>> shift


-- New: smart constructor for indices. If you have a Name 
-- in the current scope, you can make a variable instance
var :: forall a v s. (a ∈ s, SubstVar v) => Name a -> v s
var a = ivar (inj a)

--------------------------------------------------------------------
-- An abstract type for binding

-- the tag 'a' is abstract in this data structure
data Bind v c s where
    Bind :: Name a -> c (s :> a) -> Bind v c s

instance Subst v c => Subst v (Bind v c) where
    applyE s (Bind x t) = Bind x (applyE (up s) t)

-- There are two ways to create bindings. The first is 
-- to bind an existing name. 
-- This is useful in translations especially as we might already have
-- a name created from unbinding a term. We translate the body with that 
-- name in scope, and then bind exactly that name again.

-- We make the name of the bound variable the first type parameter so 
-- that we can provide it visibly when using this function (i.e. with @)
-- (in fact, it is important to do so for type class resolution)
bind :: forall a s v c. c (s :> a) -> Bind v c s
bind b = Bind Name b 

-- alternatively, we have a HOAS introduction form that is parameterized
-- by a new, fresh name 
bindFresh :: forall v c s. (forall a. Name a -> c (s :> a)) -> Bind v c s
bindFresh t = Bind Name (t Name)


-- destruct a binding, producing a fresh static name in scope
unbindWith :: Bind v c s -> (forall a. Name a -> c (s :> a) -> d) -> d
unbindWith (Bind x t) f = f x t

instance (forall s. Show (c s)) => Show (Bind v c s) where
    show (Bind x a) = "(Bind (" ++ show a ++ "))"

-----------------------------------------------------
-- past this line is a "use" of the general purpose library above
-- the example is a small dependently-typed language 

-- de Brujn 
data Exp s where
    Star :: Exp s
    Var  :: Index s -> Exp s
    App  :: Exp s -> Exp s -> Exp s
    Lam  :: Exp s -> Bind Exp Exp s -> Exp s
    Pi   :: Exp s -> Bind Exp Exp s -> Exp s
       deriving (Show)

instance SubstVar Exp where
    ivar = Var 
instance Subst Exp Exp where
    applyE s Star = Star
    applyE s (Var x) = s x
    applyE s (App e1 e2) = App (applyE s e1) (applyE s e2)
    applyE s (Lam t e) = Lam (applyE s t) (applyE s e)
    applyE s (Pi a b) = Pi (applyE s a) (applyE s b)

-----------------------------------------------------
-- operations for working with 'Exp'
-- smart weakening
-- specialized to Exp so that we don't need a type annotation
-- otherwise Haskell can't infer what type to use for 'applyE'.
weaken :: forall a b. (b ⊆ a) => Exp b -> Exp a 
weaken = applyE @Exp incl

-- convenience wrappers for two ways to create lam/pi terms
lam :: forall a s. Exp s -> Exp (s :> a) -> Exp s
lam t b = Lam t (bind b)

lamFresh :: Exp s -> (forall a. (Name a -> Exp (s :> a))) -> Exp s
lamFresh t b = Lam t (bindFresh b)

pi :: forall a s. Exp s -> Exp (s :> a) -> Exp s
pi t b = Pi t (bind b)

piFresh :: Exp s -> (forall a. (Name a -> Exp (s :> a))) -> Exp s
piFresh t b = Pi t (bindFresh b)

-----------------------------------------------------
-- Examples

-- The arrow type "A -> B" is "Pi x:A.B" in a dependently 
-- typed language. However, as x does not appear in B, we need 
-- to weaken it.
(->:) :: Exp s -> Exp s -> Exp s 
t1 ->: t2 = pi t1 $ weaken t2   

-- The type of the identity function: Pi a:*. a -> a
idTy :: Exp s 
idTy = piFresh Star $ \a -> var a ->: var a

-- An identity function "\a:*. \x:a.x"
idExp :: Exp s
idExp = lamFresh Star $ \a -> 
           lamFresh (var a) $ \x -> var x


-- >>> idTy
-- Pi Star (Bind (Pi (Var 0) (Bind (Var 1))))

-- >>> idExp
-- Lam Star (Bind (Lam (Var 0) (Bind (Var 0))))

-------------------------------------------------------------
-------------------------------------------------------------
-- parametricity translation
-- This implements Bernardy's translation from "Parametricity for dependent types"
-- Types are mapped to parametricity properties and terms are mapped to proofs of 
-- those properties. This translation is tricky to express because each variable binding 
-- in the input turns into (at least) two variable bindings in the output.  

--  [[\x:A. e]]   = \x:a.\xR: [[A]] a. [[e]]
--  [[ e1 e2 ]]   = [[e1]] e2 [[e2]]
--  [[ x ]]       = xR
--  [[ * ]]       = \x:*. Pi y:x. *
--  [[Pi x:A. B]] = \xF:(Pi x:A.B). Pi x:A. Pi xR: [[A]] a. [[B]] (xF x)

-- Overall, if  |- a : A,  we have   |- [[a]] : [[A]] a


-- For the scope translation, we use an abstract type "R" for name generation.
-- For each name "x", there is an analogous name "R x"
data R :: Tag -> Tag

type family Param (s :: Scope) :: Scope where
    Param Nil = Nil
    Param (s :> x) = Param s :> x :> R x


extend :: Sub Exp n (Param n) -> Sub Exp (n :> a) (Param (n :> a))
extend e = (up e) .>> shift

-- Given a name "x", find the name "R x"
-- multiply a variable index by two
varR :: Index n -> Index (Param n)
varR I0 = I0
varR (IS n) = IS (IS (varR n))

-- >>> varR (I0 :: Index (Nil :> a :> b))
-- 0

-- >>> varR (IS I0 :: Index (Nil :> a :> b))
-- 2


-- Take a renaming as a parameter while traversing
-- the term. This renaming multiplies the variable by two in order
-- to weaken the orginal terms appearing in the output of the translation
-- (The alternative is to pass a runtime witness of the scope as another argument
-- and use that for weakening. But in Haskell, I'd need to create a new type 
-- for this runtime witness in addition to the function that uses it for weakening.)
-- OTOH, with enough type classes, we could probably get this argument to be created 
-- and passed implicitly
param' :: forall n m. Sub Exp n (Param n) -> Exp n ->  Exp (Param n)
param' theta Star = 
    lamFresh Star $ \x -> pi (var x) Star
param' theta (Var x) = 
  -- look up the new name for the variable
  Var (varR x)
param' theta (Pi a bnd) = 
  unbindWith bnd $ \ (x :: Name x) b ->
  let -- translate domain type
      pa = param' theta a
      -- translate the body (in the extended scope)
      pb = param' (extend theta) b

  in 
    lamFresh (applyE theta (Pi a bnd)) $ \ (xF :: Name xF) -> 
       (pi @x  (applyE (skip theta) a) 
         (pi @(R x) (App (weaken pa) (var x))
            (App (weaken pb) (App (var xF) (var x)))))
param' theta (Lam ty bnd) = 
  unbindWith bnd $ \ (x :: Name x) b ->
  let 
      pty  = param' theta ty 
      pb   = param' (extend theta) b
  in 
  lam @x pty 
    (lam @(R x) (App (weaken pty) (var x)) pb)

param' theta (App f arg) = 
  App (App (param' theta f) (applyE theta arg)) (param' theta arg)


-------------------------------------------------------------------------------
--- Version 2

-- Now let's use a type class to implicitly pass the theta argument
class Theta n where  
    theta :: Sub Exp n (Param n)
instance Theta Nil where 
    theta = idE
instance Theta s => Theta (s :> a) where 
    theta = extend theta 

-- This instance is not allowed in Haskell because Param is a type family
-- instance Theta n => (n ⊆ (Param n)) where
--     incl = applyE @Exp theta
-- otherwise we could use weaken instead of "applyE theta" and 
-- "applyE (skip theta)" below

param :: forall n m. Theta n => Exp n -> Exp (Param n)
param Star = 
    lamFresh Star $ \x -> pi (var x) Star
param (Var x) = 
  -- look up the new name for the variable
  Var (varR x)
param (Pi a bnd) = 
  unbindWith bnd $ \ (x :: Name x) b ->
  let -- translate domain type
      pa = param a
      -- translate the body (in the extended scope)
      pb = param b
  in 
    lamFresh (applyE theta (Pi a bnd)) $ \ (xF :: Name xF) -> 
       (pi @x (applyE (skip theta) a) 
         (pi @(R x) (App (weaken pa) (var x))
            (App (weaken pb) (App (var xF) (var x)))))
param (Lam ty bnd) = 
  unbindWith bnd $ \ (x :: Name x) b ->
  let 
      pty  = param ty 
      pb   = param b
  in 
  lam @x pty 
    (lam @(R x)  
       (App (weaken pty) (var x)) pb)
param (App f arg) = 
  App (App (param f) (applyE theta arg)) (param arg)


-- >>> param (idTy :: Exp Nil)
-- Lam (Pi Star (Bind (Pi (Var 0) (Bind (Var 1))))) (Bind (Pi Star (Bind (Pi (App (Lam Star (Bind (Pi (Var 0) (Bind (Star))))) (Var 0)) (Bind (App (Lam (Pi (Var 1) (Bind (Var 2))) (Bind (Pi (Var 2) (Bind (Pi (App (Var 2) (Var 0)) (Bind (App (Var 3) (App (Var 2) (Var 1))))))))) (App (Var 2) (Var 1))))))))



-----------------------------------------------------
-- Version 3
--
-- This version uses functional dependencies instead of type families to 
-- all the definition of the function to use 'weaken' in all places.

class IParam s s' | s -> s' where
    denv   :: Sub Exp s s'
instance IParam Nil Nil where
    denv = idE
instance (IParam s s') => IParam (s :> a) (s' :> a :> R a) where 
    denv = (up denv) .>> shift

-- This is a dangerous instance. We only get one shot
-- with the type class search
instance {-# INCOHERENT #-} IParam s s' => s ⊆ s' where 
    incl = denv

ivarR :: IParam n n' => Index n -> Index n'
ivarR i = case (denv i) of 
            Var x -> x 
            _  -> error "not a renaming"
{-
-- if we want to avoid the (potential) error above, we can make the type class carry 
-- a proof witness and use that to convert the variable.
data DParam s s' where
    P0 :: DParam Nil Nil 
    PS :: DParam s s' -> DParam (s :> a) (s' :> a :> R a)    
ivarR = go dparam where
    go :: DParam n n' -> Index n -> Index n'
    go P0 x = case x of {}
    go (PS d) I0 = I0
    go (PS d) (IS i) = (IS (IS (go d i)))
-}


iparam :: forall n n'. (IParam n n') => Exp n -> Exp n'
iparam Star = 
    lamFresh Star $ \x -> pi (var x) Star
iparam (Var x) = 
  -- look up the new name for the variable
  Var (ivarR x)
iparam (Pi a bnd) = 
  unbindWith bnd $ \ (x :: Name x) b ->
  let -- translate domain type
      pa = iparam a
      -- translate the body (in the extended scope)
      pb = iparam b
  in 
    lamFresh (weaken (Pi a bnd)) $ \ (xF :: Name xF) -> 
       (pi @x (weaken a) 
         (pi @(R x) (App (weaken pa) (var x))
            (App (weaken pb) (App (var xF) (var x)))))
iparam (Lam ty bnd) = 
  unbindWith bnd $ \ (x :: Name x) b ->
  let 
      pty  = iparam ty 
      pb   = iparam b
  in 
  lam @x pty 
    (lam @(R x)  
       (App (weaken pty) (var x)) pb)
iparam (App f arg) = 
  App (App (iparam f) (weaken arg)) (iparam arg)



-- >>> iparam (idTy :: Exp Nil)
-- Lam (Pi Star (Bind (Pi (Var 0) (Bind (Var 1))))) (Bind (Pi Star (Bind (Pi (App (Lam Star (Bind (Pi (Var 0) (Bind (Star))))) (Var 0)) (Bind (App (Lam (Pi (Var 1) (Bind (Var 2))) (Bind (Pi (Var 2) (Bind (Pi (App (Var 3) (Var 0)) (Bind (App (Var 4) (App (Var 2) (Var 1))))))))) (App (Var 2) (Var 1))))))))
