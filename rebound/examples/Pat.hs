-- \| The untyped lambda calculus with pattern matching
--

-- |
-- Module      : Pat
-- Description : Untyped lambda calculus, with pattern matching
-- Stability   : experimental
--
-- An implementation of the untyped lambda calculus with pattern matching.
--
-- This example extends the lambda calculus with constants (like 'nil and 'cons)
-- and arbitrary pattern matching. Case expressions include a list of branches,
-- where each branch is a pattern and a right-hand side. The pattern can bind
-- multiple variables and the index ensures that the rhs matches the number of
-- variables bound in the pattern.
-- 
-- This example also includes pairs and "irrefutable patterns" i.e. let binding
-- that can deeply deconstruct cons pairs (only).
module Pat where

import Rebound

import Rebound.Bind.PatN as PatN
import qualified Rebound.Bind.Pat as Pat
import Rebound.Bind.Scoped qualified as Scoped
import Data.Maybe qualified as Maybe
import Data.Type.Equality
import Data.Fin ( Fin, f0, f1 )
import Data.Fin qualified as Fin
import Data.Vec qualified as Vec

----------------------------------------------

-- * Syntax

----------------------------------------------

-- The untyped lambda calculus extended with
-- symbols ("con"stants) and pattern matching
-- expression (case)
-- A constant applied to any number of arguments
-- is a value
data Exp (n :: Nat) where
  Var :: Fin n -> Exp n
  Lam :: Bind1 Exp Exp n -> Exp n
  App :: Exp n -> Exp n -> Exp n
  LetPair  :: Exp n -> Branch PairPat n -> Exp n
  -- ^ deep pattern matching against pairs (only)
  Con :: String -> Exp n
  -- ^ constant (or symbol) like 'cons or 'nil'
  Case :: Exp n -> [Branch Pat n] -> Exp n
  -- ^ deep pattern matching against any pattern
   

-- Each branch in a case expression is a pattern binding,
-- i.e. a data structure that binds m variables in some
-- expression body with scope n
-- Here, the variable m does not appear
-- in the result type `Branch pat n`, so is an existential.
data Branch pat (n :: Nat) where
  Branch :: SNatI m => Pat.Bind Exp Exp (pat m) n -> Branch pat n

-- Patterns for case expressions.
-- The index `m` in the pattern is the number of occurrences of
-- PVar, i.e. the number variables bound by the pattern.
-- These variables are ordered left to right.
-- For example (PCon "cons" `PApp` PVar `PApp` PVar) is the
-- representation of the pattern "cons x y", which binds two
-- variables.
-- To prevent patterns of the form "x y z", this type is split
-- into top level patterns (Pat) and applications of constants (ConApp)
data Pat (m :: Nat) where
  PVar :: Pat N1 -- binds exactly one variable
  PHead :: ConApp m -> Pat m

data ConApp (m :: Nat) where
  PCon :: String -> ConApp N0 -- binds zero variables
  PApp :: ConApp m1 -> Pat m2 -> ConApp (m2 + m1)

-- Patterns for pairs only, a special case of the above
data PairPat (m :: Nat) where
  PPVar :: PairPat N1
  PPair :: PairPat m1 -> PairPat m2 -> PairPat (m2 + m1)

----------------------------------------------

-- * Sized instance

----------------------------------------------

-- Any type that is used as a pattern must be an
-- instance of the `Sized` type class, so that the library
-- can determine the number of binding variables both
-- statically and dynamically.

-- The `Pat` type tells us how many variables are bound
-- the pattern with the index `n`. We can also recover
-- that number from the pattern itself by counting the number
-- of occurrences of `PVar`.

instance Sized (Pat m) where
  type Size (Pat m) = m

  size :: Pat m -> SNat (Size (Pat m))
  size PVar = s1
  size (PHead p) = size p


instance Sized (ConApp m) where
  type Size (ConApp m) = m

  size :: ConApp m -> SNat (Size (ConApp m))
  size (PApp p1 p2) = sPlus (size p2) (size p1)
  size (PCon s) = s0


instance Sized (PairPat m) where
  type Size (PairPat m) = m

  size :: PairPat m -> SNat (Size (PairPat m))
  size PPVar = s1
  size (PPair p1 p2) = sPlus (size p2) (size p1)


----------------------------------------------

-- * Substitution

----------------------------------------------

instance SubstVar Exp where
  var :: Fin n -> Exp n
  var = Var

instance Shiftable Exp where
  shift = shiftFromApplyE @Exp

instance Subst Exp Exp where
  applyE :: Env Exp n m -> Exp n -> Exp m
  applyE r (Var x) = applyEnv r x
  applyE r (Lam b) = Lam (applyE r b)
  applyE r (App e1 e2) = App (applyE r e1) (applyE r e2)
  applyE r (Con s) = Con s
  applyE r (Case e brs) = Case (applyE r e) (map (applyE r) brs)
  applyE r (LetPair e1 b) = LetPair (applyE r e1) (applyE r b)


instance Shiftable (Branch pat) where
  shift = shiftFromApplyE @Exp

instance Subst Exp (Branch pat) where
  applyE :: Env Exp n m -> Branch pat n -> Branch pat m
  applyE r (Branch bnd) = Branch (applyE r bnd)


----------------------------------------------
-- Example terms
----------------------------------------------

-- The identity function "λ x. x". With de Bruijn indices
-- we write it as "λ. 0"
t0 :: Exp Z
t0 = Lam (bind1 (Var f0))

-- A larger term "λ x. λy. x (λ z. z z)"
-- λ. λ. 1 (λ. 0 0)
t1 :: Exp Z
t1 =
  Lam
    ( bind1
        ( Lam
            ( bind1
                ( Var f1
                    `App` (Lam (bind1 (Var f0)) `App` Var f0)
                )
            )
        )
    )

-- "head function"
-- \x -> case x of [nil -> x ; cons y z -> y]
t2 :: Exp Z
t2 =
  Lam
    ( bind1
        ( Case
            (Var f0)
            [ Branch
                ( Pat.bind @(Pat N0)
                    (PHead (PCon "Nil"))
                    (Var f0)
                ),
              Branch
                ( Pat.bind @(Pat N2)
                    (PHead (PCon "Cons" `PApp` PVar `PApp` PVar))
                    (Var f0)
                )
            ]
        )
    )

-- a "list"  ['a','b']
t3 :: Exp Z
t3 = Con "cons" `App` Con "a" `App` (Con "cons" `App` Con "b" `App` Con "nil")

--------------------------------------------------------------

-- * Show implementation

--------------------------------------------------------------

-- >>> t0
-- λ. 0

-- >>> t1
-- λ. λ. 1 (λ. 0 0)

-- >>> t2
-- λ. case 0 of [Nil => 0,(Cons V) V => 0]

-- >>> t3
-- (cons a) ((cons b) nil)


instance Show (Exp n) where
  showsPrec :: Int -> Exp n -> String -> String
  showsPrec _ (Var x) = shows x
  showsPrec d (App e1 e2) =
    showParen (d > 0) $
      showsPrec 10 e1
        . showString " "
        . showsPrec 11 e2
  showsPrec d (Lam b) =
    showParen (d > 10) $
      showString "λ. "
        . shows (getBody1 b)
  showsPrec d (Con s) = showString s
  showsPrec d (Case e brs) =
    showParen (d > 10) $
      showString "case "
        . shows e
        . showString " of "
        . shows brs
  showsPrec d (LetPair e (Branch b)) = 
    showString "let "
    . shows (Pat.getPat b)
    . showString " = "
    . shows e
    . showString " in "
    . showsPrec d (Pat.getBody b)

instance Show (PairPat m) where
  showsPrec :: Int -> PairPat m -> String -> String
  showsPrec d PPVar = showString "V"
  showsPrec d (PPair p1 p2) =
    showParen True $
      shows p1
        . showString ","
        . shows p2

instance Show (Pat m) where
  showsPrec :: Int -> Pat m -> String -> String
  showsPrec d PVar = showString "V"
  showsPrec d (PHead p) = showsPrec d p

instance Show (ConApp m) where
  showsPrec d (PApp p1 p2) =
    showParen (d > 0) $
      showsPrec 10 p1
        . showString " "
        . showsPrec 11 p2
  showsPrec d (PCon s) = showString s


-- In a `PatBind` term, we can access the pattern with `getPat`
-- and the RHS with `getBody`
instance Show (Branch Pat n) where
  showsPrec :: Int -> Branch Pat n -> String -> String
  showsPrec d (Branch bnd) =
    shows (Pat.getPat bnd)
      . showString " => "
      . showsPrec d (Pat.getBody bnd)

--------------------------------------------------------------

-- * Eq implementation

--------------------------------------------------------------

-- We would like to derive equality for patterns, i.e. 
-- 
--     deriving instance (Eq (Pat m))
-- 
-- but because of the application case, this process fails.
-- We don't know that each subpattern binds the same
-- number of variables!


-- Therefore to compare Pats for equality, we generalize the
-- `testEquality` function from Data.Type.Equality. (This
-- class is often used for comparisons between indexed types.
-- but only works if the index is the last type parameter.
-- In our case, we need to produce an equality for the
-- first type parameter.)
-- This function can be applied, even if the number of
-- pattern-bound variables are not known to be equal.
-- (cf. m1 and m2 below). If the patterns are indeed equal,
-- then `patEq` *also* returns a proof that the indices
-- are equal. (The type `a :~: b` is a GADT with a single
-- constructor `Refl` that can only be used when a and be are
-- equal. Pattern matching on this GADT brings an equality
-- between a and b into the context of the term.)

instance PatEq (Pat m1) (Pat m2) where
  patEq PVar PVar = Just Refl
  patEq (PHead p1) (PHead p2) = do
    Refl <- patEq p1 p2
    return Refl
  patEq _ _ = Nothing

instance PatEq (ConApp m1) (ConApp m2) where
  patEq (PApp p1 p2) (PApp p1' p2') = do
    Refl <- patEq p1 p1'
    Refl <- patEq p2 p2'
    return Refl
  patEq (PCon s1) (PCon s2) | s1 == s2 = Just Refl
  patEq _ _ = Nothing

instance PatEq (PairPat m1) (PairPat m2) where
  patEq (PPair p1 p2) (PPair p1' p2') = do
    Refl <- patEq p1 p1'
    Refl <- patEq p2 p2'
    return Refl
  patEq PPVar PPVar = Just Refl
  patEq _ _ = Nothing


-- the generalized equality can be used for the usual equality
instance Eq (Pat m) where
  p1 == p2 = Maybe.isJust (patEq p1 p2)

instance Eq (PairPat m) where
  p1 == p2 = Maybe.isJust (patEq p1 p2)

instance SizeIndex PairPat p
instance SizeIndex Pat p


-- Because the Branch type is parameterized by a pattern type, `pat` of kind 
-- `Nat -> Type` we need to make some assumptions about that type to construct
-- the `Eq` instance. (1) we need to be able to test patterns for equality
-- no matter what their size is. (2) we need to know that the index *is* the 
-- size of the pattern, i.e. Size (pat m) ~ m. The `SizeIndex` class captures
-- this relationship in a way that can be quantifed over all m.
-- If we did not parameterize the `Branch` type by the pattern type, we would not
-- need this complexity.

instance (forall m. Eq (pat m),                    -- 1
          forall m. SizeIndex pat m)               -- 2
          => Eq (Branch pat n) where
  (==) :: Branch pat n -> Branch pat n -> Bool
  (Branch (p1 :: Pat.Bind Exp Exp (pat m1) n))
    == (Branch (p2 :: Pat.Bind Exp Exp (pat m2) n)) =
      case testEquality
        (size (Pat.getPat p1) :: SNat m1)
        (size (Pat.getPat p2) :: SNat m2) of
        Just Refl -> p1 == p2
        Nothing -> False


-- With the instance above the derivable equality instance
-- is alpha-equivalence
deriving instance (Eq (Exp n))


--------------------------------------------------------
-- Pattern matching code
--------------------------------------------------------

p1 :: Pat N2
p1 = PHead $ PApp (PApp (PCon "C") PVar) PVar

p2 :: Pat N2
p2 = PHead $ PApp (PApp (PCon "D") PVar) PVar

e1 :: Exp N0
e1 = App (App (Con "C") (Con "A")) (Con "B")

e2 :: Exp N0
e2 = App (App (Con "D") (Con "A")) (Con "C")

-- >>> patternMatch p1 e1
-- Just [(0,B),(1,A)]

-- >>> patternMatch p2 e1
-- Nothing

-- >>> patternMatch p1 e2
-- Nothing

-- >>> patternMatch p2 e2
-- Just [(0,C),(1,A)]


-- | Compare a "pair" pattern with a pair pattern, potentially
-- producing a substitution for all of the variables bound in the pattern.
ppatternMatch :: PairPat p -> Exp m -> Maybe (Env Exp p m)
ppatternMatch PPVar e = Just $ oneE e
ppatternMatch (PPair p1 p2) (App (App (Con "cons") e1) e2) = do
  env1 <- ppatternMatch p1 e1
  env2 <- ppatternMatch p2 e2
  withSNat (size p2) $ return (env2 .++ env1)
ppatternMatch _ _ = Nothing

-- | Compare a pattern with an expression, potentially
-- producing a substitution for all of the variables bound in the pattern.
patternMatch :: Pat p -> Exp m -> Maybe (Env Exp p m)
patternMatch PVar e = Just $ oneE e
patternMatch (PHead p) e = patternMatchApp p e

patternMatchApp :: ConApp p -> Exp m -> Maybe (Env Exp p m)
patternMatchApp (PApp p1 p2) (App e1 e2) = do
  env1 <- patternMatchApp p1 e1
  env2 <- patternMatch p2 e2
  withSNat (size p2) $ return (env2 .++ env1)
patternMatchApp (PCon s1) (Con s2) =
  if s1 == s2 then Just zeroE else Nothing
patternMatchApp _ _ = Nothing

-- Compare the scrutinee against multiple patterns and return 
-- the matching branch
findBranch :: Exp n -> [Branch Pat n] -> Maybe (Exp n)
findBranch e [] = Nothing
findBranch e (Branch bind : brs) =
  case patternMatch (Pat.getPat bind) e of
    Just r -> Just $ Pat.instantiate bind r
    Nothing -> findBranch e brs




--------------------------------------------------------
-- Eval and step
--------------------------------------------------------

{- We can write the usual operations for evaluating
   lambda terms to values -}
-- big-step evaluation
-- >>> eval t1
-- λ. λ. 1 (λ. 0 0)
-- >>> eval (t1 `App` t0)
-- λ. λ. 0 (λ. 0 0)
t4 = t2 `App` t3

-- >>> t4
-- λ. case 0 of [Nil => 0,(Cons V) V => 0] ((cons a) ((cons b) nil))
-- >>> eval t4
-- case (cons a) ((cons b) nil) of [Nil => (cons a) ((cons b) nil),(Cons V) V => 0]
eval :: Exp n -> Exp n
eval (Var x) = Var x
eval (Lam b) = Lam b
eval (App e1 e2) =
  let v = eval e2
   in case eval e1 of
        Lam b -> eval (instantiate1 b v)
        t -> App t v -- if cannot reduce, return neutral term
eval (Con s) = Con s
eval (Case e brs) =
  let v = eval e
   in case findBranch v brs of
        Just br -> eval br
        Nothing -> Case v brs -- if cannot reduce, return neutral term
eval (LetPair e (Branch b)) = 
  case ppatternMatch (Pat.getPat b) (eval e) of
    Just r -> eval (Pat.instantiate b r)
    Nothing -> error "No match!"

-- | small-step evaluation
-- >>> step (t1 `App` t0)
-- Just (λ. λ. 0 (λ. 0 0))
step :: Exp n -> Maybe (Exp n)
step (Var x) = Nothing
step (Lam b) = Nothing
step (App (Lam b) e2) = Just (instantiate1 b e2)
step (App e1 e2)
  | Just e1' <- step e1 = Just (App e1' e2)
  | Just e2' <- step e2 = Just (App e1 e2')
  | otherwise = Nothing
step (LetPair a (Branch b)) 
  | Just r <- ppatternMatch (Pat.getPat b) a
  = Just (Pat.instantiate b r)
step (LetPair e b) 
  | Just e' <- step e = Just (LetPair e' b)
  | otherwise = Nothing
step (Con s) = Nothing
step (Case e brs)
  | Just br <- findBranch e brs = Just br
  | Just e' <- step e = Just (Case e' brs)
  | otherwise = Nothing

eval' :: Exp n -> Exp n
eval' e
  | Just e' <- step e = eval' e'
  | otherwise = e

-- full normalization
-- to normalize under a lambda expression, we must first unbind
-- it and then rebind it when finished

-- >>> nf t1
-- λ. λ. 1 0
-- >>> nf (t1 `App` t0)
-- λ. λ. 0 0
nf :: Exp n -> Exp n
nf (Var x) = Var x
nf (Lam b) = Lam (bind1 (nf (getBody1 b)))
nf (App e1 e2) =
  case nf e1 of
    Lam b -> instantiate1 b (nf e2)
    t -> App t (nf e2)
nf (Con s) = Con s
nf (Case e brs) =
  let v = nf e
   in case findBranch v brs of
        Just b -> nf b
        Nothing -> Case e (map nfBr brs)
nf (LetPair e br@(Branch b)) = 
  let v = nf e in
  case ppatternMatch (Pat.getPat b) v of 
    Just r -> nf (Pat.instantiate b r)
    Nothing -> LetPair (nf e) (nfBr br)

nfBr :: (forall n. Sized (pat n)) => Branch pat n -> Branch pat n
nfBr (Branch bnd) =
  Branch (Pat.bind (Pat.getPat bnd) (nf (Pat.getBody bnd)))
