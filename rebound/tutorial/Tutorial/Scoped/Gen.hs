{-|
Module      : Tutorial.Scoped.Gen
Description : QuickCheck generators for well-scoped lambda calculus terms

Provides 'QC.Arbitrary' instances for 'Ty' and @'Tm' n@ (requiring
'SNatI' for the term instance), plus the underlying generators and
shrinkers.

The key function is 'genTm', which takes an explicit 'SNat' @n@ for the
number of free variables in scope and a size parameter bounding term
depth.  The 'SNatI' constraint on the 'Arbitrary' instance is satisfied
automatically when using @arbitrary :: Gen (Tm n)@ at a concrete @n@.
-}
module Tutorial.Scoped.Gen(Gen(..), Arbitrary(..)) where

import Tutorial.Scoped.Syntax

import Test.QuickCheck (Gen(..),Arbitrary(..))
import qualified Test.QuickCheck as QC

import qualified Data.Fin as Fin
import Data.Vec ((!))

-- * Arbitrary instance for Ty

instance QC.Arbitrary Ty  where
  arbitrary :: QC.Gen Ty
  arbitrary = QC.sized genTy

  shrink :: Ty -> [Ty]
  shrink = shrinkTy


-- | Use 'Gen' monad to generate a random type
-- 
-- The size argument ensures termination. In the base case, 
-- only small types (`Zero`, `One`) are generated.
-- 
-- >>>  QC.sample' (arbitrary :: Gen Ty)
-- [Zero,One,One,One,((One :* Zero) :+ One) :-> One,Zero,((One :+ Zero) :-> One) :* ((Zero :* One) :+ Zero),Zero,(One :* Zero) :-> ((Zero :-> Zero) :+ Zero),Zero,Zero]
--
genTy :: Int -> QC.Gen Ty
genTy sz 
  | sz <= 1   = QC.elements [ Zero, One ]
  | otherwise = QC.oneof [ pure Zero, pure One, genArr, genPair, genSum ] 
     where   
       sz' = sz `div` 2
       genArr  = (:->) <$> genTy sz' <*> genTy sz'
       genPair = (:*)  <$> genTy sz' <*> genTy sz'
       genSum  = (:+)  <$> genTy sz' <*> genTy sz'

-- | Example type, for doctest use
t :: Ty
t = ((One :+ Zero) :-> One) :* (Zero :+ Zero)

-- | Produce a list of types smaller than the argument
--
-- >>> shrinkTy ((One :* One) :+ Zero)
-- [Zero,One,One :* One,Zero,Zero :+ Zero,One :+ Zero,One :+ Zero,One :+ Zero]

shrinkTy :: Ty -> [Ty]
shrinkTy (a :-> b) = Zero : One : shrinkTwo (:->) a b
shrinkTy (a :* b)  = Zero : One : shrinkTwo (:*) a b
shrinkTy (a :+ b)  = Zero : One : shrinkTwo (:+) a b
shrinkTy _ = []

-- * Arbitrary instance for terms

-- This 
instance SNatI n => QC.Arbitrary (Tm n) where
  arbitrary :: SNatI n => QC.Gen (Tm n)
  arbitrary = QC.sized (genTm snat)
  
  shrink :: SNatI n => Tm n -> [Tm n]
  shrink = shrinkTm



-- | Generate a term of size 'sz' in scope 'n'
-- 
-- >>> QC.sample' (genTm s3 2)
-- [MatchPair (Var 1) (bind2 (Var 4)),App (Var 2) (Var 2),Inj 0 (Var 2),Pair (Var 2) (Var 1),Lam (bind1 (Var 2)),Pair (Var 0) (Var 1),Pair (Var 1) (Var 0),MatchUnit (Var 2) (Var 2),App (Var 2) (Var 0),MatchSum (Var 0) (bind1 (Var 3)) (bind1 (Var 0)),Unit]

genTm :: forall n. SNat n -> Int -> QC.Gen (Tm n)
genTm n sz =
    let
        sz' = (sz `div` 2)
        gens = [Lam <$> (bind1 <$> arbitrary <*> genTm (next n) sz'),
                App <$> genTm n sz' <*> genTm n sz',
                
                pure Unit,
                MatchUnit <$> genTm n sz' <*> genTm n sz',

                Pair <$> genTm n sz' <*> genTm n sz',
                MatchPair <$> genTm n sz' <*> (bind2 <$> arbitrary <*> arbitrary <*> genTm (next (next n)) sz'),
                
                Inj <$> QC.elements [0,1] <*> genTm n sz',
                MatchSum <$> genTm n sz'  <*> (bind1 <$> arbitrary <*> genTm (next n) sz') 
                                          <*> (bind1 <$> arbitrary <*> genTm (next n) sz')
              ]
    in
    case snat_ n of
       SZ_ -> if sz <= 1
                then pure Unit      -- smallest closed term
                else QC.oneof gens  -- arbitrary closed term
       SS_ x ->
         let
            genVar = withSNat x $ QC.elements $ map Var Fin.universe
         in
            if sz <= 1
              then QC.oneof [genVar, pure Unit]  -- either a variable in scope or unit
              else QC.oneof (genVar : gens)      -- arbitrary term in scope

-- | Shrink a well-scoped term, keeping it in the same scope @n@.
-- Variables are shrunk towards 'FZ'; other constructors drop or simplify children.
shrinkTm :: SNatI n => Tm n -> [Tm n]
shrinkTm (Var FZ) = []
shrinkTm (Var x ) = [ Var (pred x) ]
shrinkTm (Lam t)  = [ Lam (bind1 (getLocalName t) t') | t' <- shrinkTm (getBody1 t) ]
shrinkTm (App f a)  = shrinkTwo App f a
shrinkTm (Pair a b) = shrinkTwo Pair a b 
shrinkTm (MatchUnit a b) = shrinkTwo MatchUnit a b
shrinkTm (MatchPair a b) = 
   [a] ++ [ MatchPair a' b | a' <- shrink a]
       ++ [ MatchPair a (bind2 x y b') | b' <- shrink (getBody2 b)]
    where x = names ! FZ
          y = names ! (FS FZ)
          names = getLocalName2 b
shrinkTm (MatchSum a b1 b2) = 
   [a] ++ [ MatchSum a' b1 b2 | a' <- shrink a]
       ++ [ MatchSum a (bind1 (getLocalName b1) b') b2 | b' <- shrink (getBody1 b1)]
       ++ [ MatchSum a b1 (bind1 (getLocalName b2) b') | b' <- shrink (getBody1 b2)]
shrinkTm _ = []

-- | Shrink a homogeneous binary constructor by shrinking either child
shrinkTwo :: QC.Arbitrary a => (a -> a -> a) -> a -> a -> [a]
shrinkTwo f a b =
  [a,b] ++ [ f a' b | a' <- shrink a]
        ++ [ f a b' | b' <- shrink b]

-- | Shrink a binary constructor whose two arguments have different types
shrinkTwo' :: (QC.Arbitrary a, QC.Arbitrary b) => (a -> b -> a) -> a -> b -> [a]
shrinkTwo' f a b =
  [a] ++ [ f a' b | a' <- shrink a]
        ++ [ f a b' | b' <- shrink b]


