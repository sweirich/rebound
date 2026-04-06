{-|
Module      : Tutorial.Scoped.Gen
Description : QuickCheck generators for well-scoped & well-typed lambda calculus terms

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

---------------------------------------------------------------------
-- * Arbitrary instance for Types
---------------------------------------------------------------------

instance QC.Arbitrary Ty  where
  arbitrary :: QC.Gen Ty
  arbitrary = QC.sized genTy

  shrink :: Ty -> [Ty]
  shrink = shrinkTy


-- | Use 'Gen' monad to generate a random type
--
--
-- >>> QC.sample' (arbitrary :: Gen Ty)
-- [One,One :+ One,One :* (One :-> One),(One :+ One) :+ (One :-> One),((One :* One) :-> (One :-> One)) :* ((One :+ One) :-> One),((One :+ One) :-> One) :* (One :+ (One :+ One)),((One :-> One) :+ (One :-> One)) :-> ((One :+ One) :* One),((One :* One) :+ (One :* One)) :-> One,One,One :* (One :-> ((One :* One) :* (One :+ One))),One :* (((One :+ One) :* (One :* One)) :-> One)]

-- The size argument ensures termination. In the base case,
-- only small types (`One`) are generated. In each recursive call, 
-- the size is divided by two (because these are trees)
genTy :: Int -> QC.Gen Ty
genTy sz 
  | sz <= 1   = QC.elements [ One ]
  | otherwise = QC.oneof [ pure One, genArr, genPair, genSum ] 
     where   
       sz' = sz `div` 2
       genArr  = (:->) <$> genTy sz' <*> genTy sz'
       genPair = (:*)  <$> genTy sz' <*> genTy sz'
       genSum  = (:+)  <$> genTy sz' <*> genTy sz'

-- | Produce a list of types smaller than the argument
--
-- >>> shrinkTy ((One :-> One) :* (One :+ One))

shrinkTy :: Ty -> [Ty]
shrinkTy = shrink 
  where 
    shrink (a :-> b) = a : b : shrinkTwo (:->) a b
    shrink (a :* b)  = a : b : shrinkTwo (:*) a b
    shrink (a :+ b)  = a : b : shrinkTwo (:+) a b
    shrink One = []

    shrinkTwo f a b =
        [ f a' b | a' <- shrink a] ++ [ f a b' | b' <- shrink b]


---------------------------------------------------------------------
-- * Simple version: well-scoped, pure lambda calculus terms
---------------------------------------------------------------------


-- | Generate an arbitrary name for a variable
-- These are only for printing, so ok if we reuse the same name in a scope
genLocalName :: Gen LocalName
genLocalName = LocalName <$> QC.elements [ "x", "y", "z", "w", "v", "u", "t", "s" ]

-- | Identity function, the smallest closed term
tmId :: Tm n
tmId = Lam (bind1 (LocalName "x") (Var FZ))


-- | Generate a well-scoped term of language 'l' in scope 'n' of size 'sz'
-- 
-- >>> fmap height <$> QC.sample' (genScopedPureLC :: Gen (Tm Z))
-- [2,2,2,4,2,3,2,3,6,2,8]

-- >>> fmap tmSize <$> QC.sample' (genScopedPureLC :: Gen (Tm Z))
-- [2,5,2,2,5,9,2,2,5,17,2]


genScopedPureLC :: forall n. SNatI n => QC.Gen (Tm n)
genScopedPureLC = QC.sized (go snat)
    where
        go :: forall n. SNat n -> Int -> QC.Gen (Tm n)
        go n sz | sz <= 1 = genBase n
        go n sz = 
            let
              -- binders generate a random name and increment the number of free variables
              gen1 = bind1 @Tm <$> genLocalName <*> go (next n) (sz - 1)

              -- recursive calls for App divide size by two
              gen  = go n (sz `div` 2)
            in 
              QC.oneof [genBase n, Lam <$> gen1, App <$> gen <*> gen ]
            

        -- base case: either a variable or "\x.x" depending on scope
        genBase :: forall n. SNat n -> Gen (Tm n) 
        genBase SZ = return tmId
        genBase SS = Var <$> QC.elements Fin.universe


---------------------------------------------------------------------
-- * Entry point for term generators
---------------------------------------------------------------------

-- We have several controls for term generation:
-- The number of variables in scope
-- Whether the terms should be well-scoped only or also well-typed
-- Whether the terms only include constructs from the pure lambda calculus,
-- or for the full language

data Constraint = Scoped | Typed
data Language = PureLC | Full

-- | generate a term with 'n' free variables 
genTm :: SNatI n => Constraint -> Language -> Gen (Tm n)
genTm Scoped l = QC.sized (genScopedTm l snat)
genTm Typed  l = do
    ctx <- genCtx snat
    ty  <- arbitrary
    QC.sized (genTypedTm l snat ctx ty)

-- | shrink a term with 'n' free variables
shrinkTm :: SNatI n => Constraint -> Tm n -> [Tm n]
shrinkTm Scoped = shrinkScoped
shrinkTm Typed  = shrinkTyped

genVec :: forall n. SNatI n => Gen (Vec n LocalName)
genVec = gen snat where
    gen :: forall n. SNat n -> Gen (Vec n LocalName)
    gen SZ = return VNil
    gen SS = do
        v <- arbitrary
        vs <- gen snat
        return (v ::: vs)


instance SNatI n => QC.Arbitrary (Tm n) where
  arbitrary :: SNatI n => QC.Gen (Tm n)
  arbitrary = genTm Typed Full
  
  shrink :: SNatI n => Tm n -> [Tm n]
  shrink = shrinkTyped


---------------------------------------------------------------------
-- * Well-scoped generators 
---------------------------------------------------------------------


genScopedTm :: forall n. Language -> SNat n -> Int -> QC.Gen (Tm n)
genScopedTm l n sz =
    let
        gen  = genScopedTm l n (sz `div` 2)
        gen1 = bind1 @Tm <$> genLocalName <*> genScopedTm l (next n) (sz `div` 2)
        gen2 = bind2 @Tm <$> genLocalName <*> genLocalName 
                         <*> genScopedTm l (next (next n)) (sz `div` 2)
        
        gens = case l of
          PureLC -> 
              [ Lam <$> gen1,
                App <$> gen <*> gen
              ]
          Full -> 
              [ Lam <$> gen1,
                App <$> gen <*> gen,
                MatchUnit <$> gen <*> gen,
                Pair      <$> gen <*> gen,
                MatchPair <$> gen <*> gen2,
                Inj       <$> QC.elements [0,1] <*> gen,
                MatchSum  <$> gen <*> gen1 <*> gen1
              ]

        
        genVar :: forall n. SNat n -> Gen (Tm n) -> Gen (Tm n) 
        genVar SZ def = def
        genVar SS def = Var <$> QC.elements Fin.universe
            
        base = case l of 
            PureLC -> 
                genVar n (return tmId)
            Full -> 
                genVar n (return Unit)

    in if sz <= 1 
        then base
        else QC.oneof (base : gens)

---------------------------------------------------------------------
-- * Shrinking well-scoped terms
---------------------------------------------------------------------

-- | Shrink a well-scoped term, keeping it in the same scope @n@.
shrinkScoped :: SNatI n => Tm n -> [Tm n]
shrinkScoped (Lam t)  = 
    [ Lam (bind1 (getLocalName t) t') | t' <- shrinkScoped (getBody1 t) ]
shrinkScoped (App a b)  = [a,b] ++ [App a' b  | a' <- shrinkScoped a] 
                                ++ [ App a b'  | b' <- shrinkScoped b]
shrinkScoped (Pair a b) = [a,b] ++ [Pair a' b | a' <- shrinkScoped a] 
                                ++ [ Pair a b' | b' <- shrinkScoped b]
shrinkScoped (Inj i a)  = [a] ++ [Inj i a' | a' <- shrinkScoped a]
shrinkScoped (MatchUnit a b) = [a,b] ++ [ MatchUnit a' b | a' <- shrinkScoped a] 
                                     ++ [ MatchUnit a b' | b' <- shrinkScoped b]
shrinkScoped (MatchPair a b) = 
   [a] ++ [ MatchPair a (bind2 x y b') | b' <- shrinkScoped (getBody2 b)]
    where x = names ! FZ
          y = names ! (FS FZ)
          names = getLocalName2 b
shrinkScoped (MatchSum a b1 b2) = 
   [a] ++ [ MatchSum a (bind1 (getLocalName b1) b') b2 | b' <- shrinkScoped (getBody1 b1)]
       ++ [ MatchSum a b1 (bind1 (getLocalName b2) b') | b' <- shrinkScoped (getBody1 b2)]
shrinkScoped (Var x) = [] 
shrinkScoped Unit = []

---------------------------------------------------------------------
-- * Well-typed term generators
---------------------------------------------------------------------

-- | Generate a random typing context: one type per free variable in scope
genCtx :: SNat n -> QC.Gen (Vec n Ty)
genCtx n = case snat_ n of
    SZ_  -> pure VNil
    SS_ m -> (:::) <$> arbitrary <*> genCtx m


-- | Generate a well-typed term of type 'ty' in scope 'n' with typing context 'ctx'.
--
-- The context 'ctx' maps each de Bruijn index to its type.  The generator is
-- type-directed: it only produces terms that have exactly type 'ty' under 'ctx'.
-- The size argument bounds term depth to ensure termination.
-- When no generators apply and no variable matches, falls back to 'Unit'.
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
        then pure Unit   -- fallback when no generators apply at small size
        else QC.oneof allGens

-- | Shrink a well-typed term, keeping it in the same scope @n@.
-- If the input is well-typed, then the output will be well-typed, but not necessarily
-- with the same type
shrinkTyped :: SNatI n => Tm n -> [Tm n]
shrinkTyped = shrink 
  where
    shrink :: SNatI n => Tm n -> [Tm n]
    shrink (Lam t)    = [Lam (bind1 (getLocalName t) t') | t' <- shrink (getBody1 t)]
    shrink (App a b)  = [a,b] 
    shrink (Pair a b) = [a,b] ++ shrinkTwo Pair a b 
    shrink (Inj i a)  = [a] ++ [Inj i a' | a' <- shrink a]
    shrink (MatchUnit a b) = [a] ++ [MatchUnit a b' | b' <- shrink b] 
    shrink (MatchPair a b) = 
        [a] ++ [ MatchPair a (bind2 x y b') | b' <- shrink (getBody2 b)]
                 where x = names ! FZ
                       y = names ! (FS FZ)
                       names = getLocalName2 b
    shrink (MatchSum a b1 b2) = 
        [a] ++ [ MatchSum a (bind1 (getLocalName b1) b') b2 | b' <- shrink (getBody1 b1)]
            ++ [ MatchSum a b1 (bind1 (getLocalName b2) b') | b' <- shrink (getBody1 b2)]
    shrink _ = []
   
    shrinkTwo f a b =
            [ f a' b | a' <- shrink a] ++ [ f a b' | b' <- shrink b]




