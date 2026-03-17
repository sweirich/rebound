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
module Tutorial.Scoped.Gen where

import Tutorial.Scoped.Syntax

import Test.QuickCheck (Gen(..),Arbitrary(..))
import qualified Test.QuickCheck as QC

import qualified Data.Fin as Fin
import Data.Vec (Vec(..), (!))

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
  | sz <= 1   = QC.elements [ One ]
  | otherwise = QC.oneof [ pure One, genArr, genPair, genSum ] 
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
shrinkTy (a :-> b) = One : shrinkTwo (:->) a b
shrinkTy (a :* b)  = One : shrinkTwo (:*) a b
shrinkTy (a :+ b)  = One : shrinkTwo (:+) a b
shrinkTy _ = []

-- * Arbitrary instance for terms

-- This 
instance SNatI n => QC.Arbitrary (Tm n) where
  arbitrary :: SNatI n => QC.Gen (Tm n)
  arbitrary = genTypedFull
  
  shrink :: SNatI n => Tm n -> [Tm n]
  shrink = shrinkTm


data Language = PureLC | Full

genPureLC :: SNatI n => QC.Gen (Tm n)
genPureLC = QC.sized (genTm PureLC snat)

genPureLCVal :: SNatI n => QC.Gen (Tm n)
genPureLCVal = QC.sized (genVal PureLC snat)

genFull :: SNatI n => QC.Gen (Tm n)
genFull = QC.sized (genTm PureLC snat)

genFullVal :: SNatI n => QC.Gen (Tm n)
genFullVal = QC.sized (genVal Full snat)

genLocalName :: QC.Gen LocalName
genLocalName = LocalName <$> QC.elements [ "x", "y", "z", "w", "v", "u", "t", "s" ]

-- | Generate a *value* of size 'sz' in scope 'n' for either just the lambda calculus (with unit)
-- or the full language
genVal :: forall n. Language -> SNat n -> Int -> QC.Gen (Tm n)
genVal l n sz = 
    let gen  = genVal l n (sz `div` 2)
        gen1 = bind1 @Tm <$> genLocalName <*> genTm l (next n) (sz `div` 2)
        gen2 = bind2 @Tm <$> genLocalName <*> genLocalName <*> genTm l (next (next n)) (sz `div` 2)
        
        gens = case l of
          PureLC -> 
              [ Lam <$> gen1 ]
          Full -> 
              [ Lam <$> gen1,
                pure Unit,
                Pair <$> gen <*> gen,
                Inj  <$> QC.elements [0,1] <*> gen
              ]
    in
    -- case analysis on number of free variables
    case snat_ n of
       SZ_ -> if sz <= 1
                then pure (Lam (bind1 (LocalName "x") (Var FZ)))  -- smallest closed value
                else QC.oneof gens  -- arbitrary closed value
       SS_ x ->
         let
            genVar = withSNat x $ QC.elements $ map Var Fin.universe
         in
            if sz <= 1
              then QC.oneof [genVar, pure Unit]  -- either a variable in scope or unit
              else QC.oneof (genVar : gens)      -- arbitrary value in scope


-- | Generate a term of size 'sz' in scope 'n' for either just the lambda calculus (with unit)
-- or the full language
-- 
-- >>> fmap height <$> QC.sample' (genPureLC :: Gen (Tm Z))

genTm :: forall n. Language -> SNat n -> Int -> QC.Gen (Tm n)
genTm l n sz =
    let
        gen  = genTm l n (sz `div` 2)
        gen1 = bind1 @Tm <$> genLocalName <*> genTm l (next n) (sz `div` 2)
        gen2 = bind2 @Tm <$> genLocalName <*> genLocalName <*> genTm l (next (next n)) (sz `div` 2)
        
        gens = case l of
          PureLC -> 
              [ Lam <$> gen1,
                App <$> gen <*> gen
              ]
          Full -> 
              [ Lam <$> gen1,
                App <$> gen <*> gen,
                pure Unit,
                MatchUnit <$> gen <*> gen,
                Pair      <$> gen <*> gen,
                MatchPair <$> gen <*> gen2,
                Inj       <$> QC.elements [0,1] <*> gen,
                MatchSum  <$> gen <*> gen1 <*> gen1
              ]
    in
    -- case analysis on number of free variables
    case snat_ n of
       SZ_ -> if sz <= 1
                then pure (Lam (bind1 (LocalName "x") (Var FZ)))  -- smallest closed term
                else QC.oneof gens  -- arbitrary closed term
       SS_ x ->
         let
            genVar = withSNat x $ QC.elements $ map Var Fin.universe
         in
            if sz <= 1
              then QC.oneof [genVar, pure Unit]             -- either a variable in scope or unit
              else QC.oneof (genVar : gens)      -- arbitrary term in scope

-- * Well-typed term generators

-- | Generate a random typing context: one type per free variable in scope
genCtx :: SNat n -> QC.Gen (Vec n Ty)
genCtx n = case snat_ n of
    SZ_  -> pure VNil
    SS_ m -> (:::) <$> arbitrary <*> genCtx m

genTypedPureLC :: SNatI n => QC.Gen (Tm n)
genTypedPureLC = do
    ctx <- genCtx snat
    ty  <- arbitrary
    QC.sized (genTypedTm PureLC snat ctx ty)

genTypedFull :: SNatI n => QC.Gen (Tm n)
genTypedFull = do
    ctx <- genCtx snat
    ty  <- arbitrary
    QC.sized (genTypedTm Full snat ctx ty)

-- | Generate a well-typed term of type 'ty' in scope 'n' with typing context 'ctx'.
--
-- The context 'ctx' maps each de Bruijn index to its type.  The generator is
-- type-directed: it only produces terms that have exactly type 'ty' under 'ctx'.
-- The size argument bounds term depth to ensure termination.
-- When the target type is uninhabited (e.g. 'Zero') and no variable matches,
-- falls back to 'Unit'.
genTypedTm :: forall n. Language -> SNat n -> Vec n Ty -> Ty -> Int -> QC.Gen (Tm n)
genTypedTm l n ctx ty sz =
    let
        sz' = sz `div` 2
        gen ty' = genTypedTm l n ctx ty' sz'

        -- Variables in scope whose type matches the target type
        matchingVars = withSNat n [ Var i | i <- Fin.universe, ctx ! i == ty ]

        -- Introduction forms, selected by target type
        introGens = case ty of
            One       -> [ pure Unit ]
            Zero      -> []
            (a :-> b) ->
                [ Lam <$> (bind1 @Tm <$> genLocalName
                                      <*> genTypedTm l (next n) (a ::: ctx) b sz') ]
            (a :* b)  -> case l of
                PureLC -> []
                Full   -> [ Pair <$> gen a <*> gen b ]
            (a :+ b)  -> case l of
                PureLC -> []
                Full   -> [ Inj 0 <$> gen a, Inj 1 <$> gen b ]

        -- Elimination forms, only included when sz > 1
        elimGens
            | sz <= 1   = []
            | otherwise =
                let appGen = do
                        a <- QC.sized genTy
                        App <$> gen (a :-> ty) <*> gen a
                in case l of
                    PureLC -> [ appGen ]
                    Full   ->
                        [ appGen
                        , MatchUnit <$> gen One <*> gen ty
                        , do a <- QC.sized genTy
                             b <- QC.sized genTy
                             -- FZ maps to b (2nd component), FS FZ maps to a (1st)
                             MatchPair <$> gen (a :* b)
                                       <*> (bind2 @Tm <$> genLocalName <*> genLocalName
                                                      <*> genTypedTm l (next (next n))
                                                                     (b ::: a ::: ctx) ty sz')
                        , do a <- QC.sized genTy
                             b <- QC.sized genTy
                             MatchSum <$> gen (a :+ b)
                                      <*> (bind1 @Tm <$> genLocalName
                                                     <*> genTypedTm l (next n) (a ::: ctx) ty sz')
                                      <*> (bind1 @Tm <$> genLocalName
                                                     <*> genTypedTm l (next n) (b ::: ctx) ty sz')
                        ]

        varGens = if null matchingVars then [] else [ QC.elements matchingVars ]

        allGens = introGens ++ elimGens ++ varGens
    in
    if null allGens
        then pure Unit   -- fallback for uninhabited types (e.g. Zero) at small size
        else QC.oneof allGens

-- | Shrink a well-scoped term, keeping it in the same scope @n@.
-- If the input is well-typed, then the output will be well-typed, but not necessarily
-- with the same type
shrinkTm :: SNatI n => Tm n -> [Tm n]
shrinkTm (Lam t)  = [ Lam (bind1 (getLocalName t) t') | t' <- shrinkTm (getBody1 t) ]
shrinkTm (App f a)  = [f,a] 
shrinkTm (Pair a b) = shrinkTwo Pair a b 
shrinkTm (Inj i a)  = [a]
shrinkTm (MatchUnit a b) = [a, MatchUnit Unit b] ++ [MatchUnit a b' | b' <- shrink b] 
shrinkTm (MatchPair a b) = 
   [a] ++ [ MatchPair a (bind2 x y b') | b' <- shrink (getBody2 b)]
    where x = names ! FZ
          y = names ! (FS FZ)
          names = getLocalName2 b
shrinkTm (MatchSum a b1 b2) = 
   [a] ++ [ MatchSum a (bind1 (getLocalName b1) b') b2 | b' <- shrink (getBody1 b1)]
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


