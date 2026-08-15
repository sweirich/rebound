{- 

  Part 2: Another "Pearl" -- dependently-typed environments

-}

module Talks.Hs26.Talk3 where

import Data.Fin
import Rebound.Lib


data Tm n =
    Var (Fin n)
  | App (Tm n) (Tm n)
  | Lam (Tm (S n))
  deriving (Eq, Show)

applyE :: Env m n -> Tm m -> Tm n
applyE env (Var x)     = env ! x
applyE env (App t1 t2) = App (applyE env t1) (applyE env t2)
applyE env (Lam t)     = Lam (applyE (up env) t)

------------------------------------------------------------
-- * SkewList implementation
------------------------------------------------------------

data Env m n where 
  Nil  :: Env Z n
  Cons :: Tm n -> Env m n -> Env (S m) n
  Id   :: Env m m  
  Inc  :: SNat k -> Env m n -> Env m (k + n)


up :: forall n m. Env n m -> Env (S n) (S m)
up s = Var FZ .: Inc s1 s 

shift :: SNat k -> Tm n -> Tm (k + n)
shift k = applyE (Inc k Id) 

------------------------------------------------------------
-- * Look up
------------------------------------------------------------


(!) :: Env m n -> Fin m -> Tm n
env ! x = applyRec s0 env x

-- >>> :t shiftN
-- shiftN :: SNat n -> Fin m -> Fin (n + m)

-- >>> :t axiomAssoc
-- axiomAssoc :: (p + (m + n)) :~: ((p + m) + n)

-- | As we traverse the list, accumulate the shifting amount and 
-- apply it all at once.
applyRec :: forall acc m n.
    SNat acc -> Env m n -> Fin m -> Tm (acc + n)
applyRec acc s i = 
    case s of 

        Id  -> Var (shiftN acc i)

        Nil -> case i of {}

        Cons t s -> case i of 
            FZ   -> shift acc t  
            FS j -> applyRec acc s j

        Inc (k :: SNat k) (env :: Env m n1) ->
            let 
                ret :: Tm ((acc + k) + n1)
                ret = applyRec (sPlus acc k) env i
            in case axiomAssoc @acc @k @n1 of
              Refl -> (ret :: Tm (acc + (k + n1)))




zeroE :: Env Z n
zeroE = Nil

(.:) :: Tm n -> Env m n -> Env (S m) n
(.:) = Cons


inc :: forall k m n. SNat k -> Env m n -> Env m (k + n)
inc k (Inc (j :: SNat j) (s :: Env m n1))
 | Refl <- axiomAssoc @k @j @n1 
 = Inc (sPlus k j) s
inc k s = Inc k s 

------------------------------------------------------------
-- * Test cases
------------------------------------------------------------

-- Id leaves a variable alone
check_id_var :: Bool
check_id_var = applyE (Id :: Env N2 N2) (Var f0) == Var f0

-- Id leaves a compound term (with a binder) alone
check_id_term :: Bool
check_id_term = applyE (Id :: Env N2 N2) t0 == t0
  where t0 = App (Var f0) (Lam (App (Var FZ) (Var (FS f0))))

-- Inc s1 Id is the "shift by 1" renaming
check_shift :: Bool
check_shift = applyE (Inc s1 Id :: Env N1 N2) (Var f0) == Var (FS f0)

-- (!) picks out the head of a Cons
check_cons_head :: Bool
check_cons_head = (Cons (Var f0) Nil :: Env N1 N1) ! FZ == Var f0

-- (!) skips over the head into the tail
check_cons_tail :: Bool
check_cons_tail =
  (Cons (Var f0) (Cons (Var f0) Nil) :: Env N2 N1) ! FS FZ == Var f0

-- an Inc wrapped around a Cons still shifts the term found at the head
check_inc_over_cons :: Bool
check_inc_over_cons =
  let env = Inc s1 (Cons (Var f0) Nil :: Env N1 N1) :: Env N1 N2
   in env ! FZ == Var (FS f0)

-- up leaves the newly bound variable (index 0) alone ...
check_up_zero :: Bool
check_up_zero = up (Id :: Env N2 N2) ! FZ == Var FZ

-- ... and shifts every other entry by one
check_up_succ :: Bool
check_up_succ =
  let s = Cons (Var f0) Nil :: Env N1 N1
   in up s ! FS FZ == applyE (Inc s1 Id :: Env N1 N2) (s ! FZ)

-- applyE recurses through a binder, using 'up' to shift the substitution
check_applyE_lam :: Bool
check_applyE_lam = applyE s t == expected
  where
    s = Cons (App (Var f0) (Var f0)) Nil :: Env N1 N1  -- var 0 |-> (0 0)
    t = Lam (Var (FS f0)) :: Tm N1                      -- \x. (outer var 0)
    expected = Lam (App (Var (FS f0)) (Var (FS f0))) :: Tm N1



----------------------------------------------------------- 
-- ** What have we learned?
----------------------------------------------------------- 





hmmm :: Int :~: Bool
hmmm = hmmm 

----------------------------------------------------------- 
-- ** More pattern binding
----------------------------------------------------------- 

{-
data Exp (n :: Nat)
  = Var (Fin n)
  | Lambda (Branch n)  -- case lambda
  | App (Exp n) (Exp n)
  | Star
  | Pi (Exp n) (Bind1 n)
  | Sigma (Exp n) (Bind1 n)
  | Pair (Exp n) (Exp n)
  | Annot (Exp n) (Exp n)
      deriving (Generic1)

-- | A single branch in a case lambda
data Branch (n :: Nat)
  = forall p. Branch (BindP p n)

-- | Patterns, which may include embedded type annotations
-- `p` is the number of variables bound by the pattern
-- `n` is the number of free variables in type annotations in the pattern
data Pat (p :: Nat) (n :: Nat) where
  PVar :: Pat N1 n
  -- Patterns are "telescopic"
  -- In Pair pattern, we increase the scope so that variables
  -- bound in the left subterm can be referred to in the right subterm
  PPair :: Pat p1 n -> Pat p2 (p1 + n) -> Pat (p2 + p1) n
  -- Patterns can also include type annotations
  PAnnot :: Pat p n -> Exp n -> Pat p n

-- type abbreviations for convenience
type Bind1 n   = Bind Exp Exp LocalName1 n   
type BindP p n = Bind Exp Exp (Pat p) n

-------------------------------------------------------
-- definitions for pattern matching
-------------------------------------------------------

eval :: Exp n -> Exp n
eval (Var x) = Var x
eval (Lambda b) = Lambda b
eval (App e1 e2) =
  let v = eval e2
   in case eval e1 of
        Lambda (Branch b) -> case patternMatch (getPat b) v of
          Just r -> eval (instantiate b r)
          Nothing -> error "pattern match failure"
        t -> App t v
eval Star = Star
eval (Pi a b) = Pi a b
eval (Sigma a b) = Sigma a b
eval (Annot a t) = eval a
eval (Pair a b) = Pair a b

-- | Compare a pattern with an expression, potentially
-- producing a substitution for all of the variables
-- bound in the pattern
patternMatch :: Pat p n -> Exp n -> Maybe (Env Exp p n)
patternMatch PVar e = Just $ oneE e
patternMatch (PPair p1 p2) (Pair e1 e2) =
  -- two append operations require implicit sizes in the context
  withSNat (size p1) $ withSNat (size p2) $ do
    env1 <- patternMatch p1 e1
    -- NOTE: substitute in p2 with env1 before pattern matching
    -- NOTE: we are in scope n, so need to prepend identity env
    -- to leave those variables alone.
    env2 <- patternMatch (applyE (env1 .++ idE) p2) e2
    return (env2 .++ env1)
-- ignore type annotates when pattern matching
patternMatch (PAnnot p _) e = patternMatch p e
patternMatch p (Annot e _) = patternMatch p e
patternMatch _ _ = Nothing


-------------------------------------------------------
-- definitions for pattern matching
-------------------------------------------------------

instance Sized (Pat p n) where
  type Size (Pat p n) = p
  size :: Pat p n -> SNat p
  size PVar = s1
  size (PPair p1 p2) = sPlus (size p2) (size p1)
  size (PAnnot p _) = size p

-- Because Pat is a scope-indexed pattern, we need to also 
-- instantiate the `ScopedSized` class
instance ScopedSized (Pat p) where
  type ScopedSize (Pat p) = p


----------------------------------------------
-- * Subst instances
----------------------------------------------

instance SubstVar Exp where
  var = Var

instance Subst Exp Exp where
  isVar (Var x) = Just (Refl, x)
  isVar _ = Nothing


-- This definition cannot be generic because Pat is a GADT
instance Subst Exp (Pat p) where
  applyE :: Env Exp n m -> Pat p n -> Pat p m
  applyE r PVar = PVar
  -- need to account for new pattern variables from p1 bound in p2
  applyE r (PPair p1 p2) = PPair (applyE r p1) (applyE (upN (size p1) r) p2)
  applyE r (PAnnot p t) = PAnnot (applyE r p) (applyE r t)

-- This definition also cannot be generic due to the existential
instance Subst Exp Branch where
  applyE :: Env Exp n m -> Branch n -> Branch m
  applyE r (Branch b) = Branch (applyE r b)


----------------------------------------------
-- * Alpha-equivalence
----------------------------------------------


-- The derivable equality instance is alpha-equivalence
deriving instance (Eq (Exp n))

instance Eq (Bind1 n) where
    (==) :: Bind1 n -> Bind1 n -> Bool
    b1 == b2 = getBody b1 == getBody b2

instance PatEq (Pat p1 n) (Pat p2 n) where
  patEq :: Pat p1 n -> Pat p2 n -> Maybe (p1 :~: p2)
  patEq PVar PVar = Just Refl
  patEq (PPair p1 p2) (PPair p1' p2') = do
    Refl <- patEq p1 p1'
    Refl <- patEq p2 p2'
    return Refl
  patEq (PAnnot p1 p2) (PAnnot p1' p2') = do
    Refl <- patEq p1 p1'
    guard (p2 == p2')
    return Refl
  patEq _ _ = Nothing

instance Eq (Branch n) where
  (==) :: Branch n -> Branch n -> Bool
  (Branch (p1 :: Bind Exp Exp (Pat m1) n))
    == (Branch (p2 :: Bind Exp Exp (Pat m2) n)) =
      case testEquality
        (size (getPat p1) :: SNat m1)
        (size (getPat p2) :: SNat m2) of
        Just Refl -> p1 == p2
        Nothing -> False


----------------------------------------------
-- LocalName1 definitions
----------------------------------------------

data LocalName1 n where
    LN1 :: LocalName -> LocalName1 n
      deriving (Generic1)

instance Sized (LocalName1 p) where
  type Size (LocalName1 p) = N1
  size :: LocalName1 p -> SNat N1
  size (LN1 _) = s1
  
instance ScopedSized LocalName1 where
  type ScopedSize LocalName1 = N1 

instance SubstVar a => Subst a LocalName1 where

instance FV LocalName1 where

instance Strengthen LocalName1 where

-}
