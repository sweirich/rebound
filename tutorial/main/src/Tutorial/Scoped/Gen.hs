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
import qualified Tutorial.Scoped.ScopeCheck as SC
import qualified Rebound.Bind.Pat as Pat

import Test.QuickCheck (Gen(..),Arbitrary(..),Testable,Property)
import qualified Test.QuickCheck as QC

import qualified Data.Fin as Fin
import Data.Vec (Vec(..), (!))
import qualified Data.Vec as Vec

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
-- [One,One :+ One,One,(One :+ One) :+ (One :* One),((One :* One) :* (One :* One)) :* ((One :* One) :+ (One :* One)),(One :+ One) :* ((One :-> One) :-> (One :+ One)),((One :* One) :-> (One :* One)) :-> ((One :* One) :+ (One :* One)),One :-> One,(((One :+ One) :+ One) :-> ((One :+ One) :* One)) :* (One :+ ((One :-> One) :-> One)),One :-> (((One :* One) :+ (One :* One)) :* One),(((One :-> One) :-> (One :* One)) :+ One) :+ One]


-- The size argument ensures termination. In the base case,
-- only small types (`One`) are generated. In each recursive call, 
-- the size is divided by two (because these are trees)
genTy :: Int -> QC.Gen Ty
genTy sz 
  | sz <= 1   = return One 
  | otherwise = QC.oneof [ return One, genArr, genPair, genSum ] 
     where   
       sz' = sz `div` 2
       genArr  = (:->) <$> genTy sz' <*> genTy sz'
       genPair = (:*)  <$> genTy sz' <*> genTy sz'
       genSum  = (:+)  <$> genTy sz' <*> genTy sz'

-- | Produce a list of types smaller than the argument
--
-- >>> shrinkTy ((One :-> One) :* (One :+ One))
-- [One :-> One,One :+ One,One :* (One :+ One),One :* (One :+ One),(One :-> One) :* One,(One :-> One) :* One]

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
-- * Simple version: generate and shrink well-scoped, pure lambda calculus terms
---------------------------------------------------------------------


-- | Generate an arbitrary name for a variable
-- These are only for printing, so ok if we reuse the same name in a scope
genLocalName :: Gen LocalName
genLocalName = QC.elements (map LocalName [ "x", "y", "z", "w", "v", "u", "t", "s" ])

-- | Identity function, the smallest closed term
tmId :: Tm n
tmId = Lam (bind1 (LocalName "x") (Var FZ))


-- For variables we need to know the number of variables in scope to 
-- be able to generate an arbitrary variable. 

-- >>> :info SNat
-- type SNat :: Nat -> *
-- data SNat n where
--   SZ :: SNat 'Z
--   SS :: SNatI n1 => SNat ('S n1)
--   	-- Defined in ‘Data.Type.Nat’

-- >>> :t snat
-- snat :: SNatI n => SNat n


--- >>> (Fin.universe :: [Fin N3])
-- [0,1,2]


-- For small terms: generate either a variable or "\x.x" depending on scope
genBase :: forall n. SNat n -> Gen (Tm n) 
genBase SZ = return tmId
genBase SS = QC.elements (map Var Fin.universe)

-- >>> QC.sample' (genBase (snat :: SNat N3))
-- [Var 0,Var 1,Var 1,Var 2,Var 2,Var 1,Var 1,Var 2,Var 0,Var 1,Var 1]


-- | Generate a well-scoped term of language 'l' in scope 'n' of size 'sz'
-- 
genScopedPureLC :: forall n. SNatI n => QC.Gen (Tm n)
genScopedPureLC = QC.sized go
    where
        go :: forall n. SNatI n => Int -> QC.Gen (Tm n)
        go sz | sz <= 1 = genBase snat
        go sz = 
            let
              -- binders generate a random name and increment the number of free variables
              gen1 = bind1 @Tm <$> genLocalName <*> go (sz - 1)

              -- recursive calls for App divide size by two
              gen  = go (sz `div` 2)
            in 
              QC.oneof [genBase snat, Lam <$> gen1, App <$> gen <*> gen ]
            

        
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
genTm Typed  l = QC.sized (\sz -> do
    ctx <- genCtx snat
    ty  <- genTy sz
    genTypedTm l snat ctx ty sz)

-- | shrink a term with 'n' free variables
shrinkTm :: SNatI n => Constraint -> Tm n -> [Tm n]
shrinkTm Scoped = shrinkScoped
shrinkTm Typed  = shrinkTyped

-- | generate a vector of names
genVec :: forall n. SNatI n => Gen (Vec n LocalName)
genVec = gen snat where
    gen :: forall n. SNat n -> Gen (Vec n LocalName)
    gen SZ = return VNil
    gen SS = do
        v <- arbitrary
        vs <- gen snat
        return (v ::: vs)

---------------------------------------------------------------------
-- * Arbitrary instance
---------------------------------------------------------------------

-- by default generate well-typed terms from the full language

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
            

        genMatchUnit = do
            e  <- gen
            e' <- gen
            return (Match e [Branch (Pat.bind PUnit e')])
        genMatchPair = do
            e    <- gen
            ln1  <- genLocalName
            ln2  <- genLocalName
            body <- genScopedTm l (next (next n)) (sz `div` 2)
            return (Match e [Branch (Pat.bind (PPair (PVar ln1) (PVar ln2)) body)])
        genMatchSum = do
            e   <- gen
            ln1 <- genLocalName
            ln2 <- genLocalName
            b1  <- genScopedTm l (next n) (sz `div` 2)
            b2  <- genScopedTm l (next n) (sz `div` 2)
            return (Match e [ Branch (Pat.bind (PInj 0 (PVar ln1)) b1)
                            , Branch (Pat.bind (PInj 1 (PVar ln2)) b2) ])

        gens = case l of
          PureLC ->
              [ Lam <$> gen1,
                App <$> gen <*> gen
              ]
          Full ->
              [ Lam <$> gen1,
                App <$> gen <*> gen,
                genMatchUnit,
                Pair <$> gen <*> gen,
                genMatchPair,
                Inj <$> QC.elements [0,1] <*> gen,
                genMatchSum
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
shrinkScoped (Match e brs) =
    [e] ++ [Match e' brs | e' <- shrinkScoped e]
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


genPureTy :: Int -> QC.Gen Ty
genPureTy sz 
  | sz <= 1   = return One 
  | otherwise = QC.oneof [ return One, genArr ] 
     where   
       sz' = sz `div` 2
       genArr  = (:->) <$> genTy sz' <*> genTy sz'


data SomePat where
    SomePat :: Pat m -> Vec m Ty -> SomePat

-- generate a random list of exhaustive patterns for the given type
genPats :: Ty -> Int -> QC.Gen [SomePat]
genPats ty sz = 
    let 
        genVar ty = do
            x <- genLocalName 
            return [SomePat (PVar x) (ty ::: VNil)]
        genUnit = 
            return [SomePat PUnit VNil]

        genPair a b = do 
            (ps1 :: [SomePat]) <- genPats a (sz `div` 2) 
            (ps2 :: [SomePat]) <- genPats b (sz `div` 2) 
            return $ do
                  (SomePat p1 ctx1) <- ps1
                  (SomePat p2 ctx2) <- ps2
                  [SomePat (PPair p1 p2) (ctx2 Vec.++ ctx1)]
        genSum a b = do 
            ps1 <- genPats a (sz `div` 2)
            ps2 <- genPats b (sz `div` 2)
            return $ do
                  SomePat pa ctxa <- ps1
                  SomePat pb ctxb <- ps2
                  [SomePat (PInj 0 pa) ctxa, SomePat (PInj 1 pb) ctxb]

    in case ty of
          One     -> QC.oneof [genVar ty, genUnit]
          a :* b  -> QC.oneof [genVar ty, genPair a b]
          a :+ b  -> QC.oneof [genVar ty, genSum a b]
          a :-> b -> genVar ty


-- | Generate a well-typed term of type 'ty' in scope 'n' with typing context 'ctx'.
--
-- The context 'ctx' maps each de Bruijn index to its type.  The generator is
-- type-directed: it only produces terms that have exactly type 'ty' under 'ctx'.
-- The size of the type bounds the depth of generated values
-- The sz argument bounds the size of generated types for elimination forms

genTypedTm :: forall n. Language -> SNat n -> Vec n Ty -> Ty -> Int -> QC.Gen (Tm n)
genTypedTm l n ctx ty sz =
    let
        
        gen ty' = genTypedTm l n ctx ty' (sz `div` 2)

        -- Variables in scope whose type matches the target type
        matchingVars = withSNat n [ Var i | i <- Fin.universe, ctx ! i == ty ]

        genVal :: forall n. SNat n -> Vec n Ty -> Ty -> Gen (Tm n)
        genVal n ctx ty = case ty of 
            One -> pure Unit
            (a :-> b) ->
                Lam <$> (bind1 @Tm <$> genLocalName
                                   <*> genVal (next n) (a ::: ctx) b)
            (a :* b)  -> 
                Pair <$> genVal n ctx a <*> genVal n ctx b
            (a :+ b)  ->  
                QC.oneof [Inj 0 <$> genVal n ctx a, Inj 1 <$> genVal n ctx b ]

        -- Introduction forms, selected by target type
        introGens = case ty of
            One       -> [ pure Unit ]
            (a :-> b) ->
                [ Lam <$> (bind1 @Tm <$> genLocalName
                      <*> genTypedTm l (next n) (a ::: ctx) b (sz `div` 2)) ]
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
                        a <- genTy (sz `div` 2)
                        App <$> gen (a :-> ty) <*> gen a

                    genBranch ty (SomePat p ctx2) = do
                        e <- genTypedTm l (sPlus (size p) n) (ctx2 Vec.++ ctx) ty (sz `div` 2)
                        return (Branch (Pat.bind @_ @_ @_ @n p e))

                    genMatch = do
                        a <- genTy (sz `div` 2) 
                        e <- gen a
                        ps <- genPats a (sz `div` 2)
                        brs <- mapM (genBranch ty) ps
                        return (Match e brs)

                in case l of
                    PureLC -> [ appGen ]
                    Full   ->
                        [ appGen
                        , genMatch
                        ]
        varGens = if null matchingVars then [] else [ QC.elements matchingVars ]
        
        allGens = introGens ++ elimGens ++ varGens
    in
    if null allGens
        then genVal n ctx ty
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
    shrink (Match e _) = [e]
    shrink _ = []
   
    shrinkTwo f a b =
            [ f a' b | a' <- shrink a] ++ [ f a b' | b' <- shrink b]


--- >>> :info QC.Args
-- type Args :: *
-- data Args
--   = Args {replay :: Maybe (QCGen, Int),
--           maxSuccess :: Int,
--           maxDiscardRatio :: Int,
--           maxSize :: Int,
--           chatty :: Bool,
--           maxShrinks :: Int}
--   	-- Defined in ‘Test.QuickCheck.Test’
-- instance Read Args -- Defined in ‘Test.QuickCheck.Test’
-- instance Show Args -- Defined in ‘Test.QuickCheck.Test’



-- | Test a property on a closed term
forAll0 :: Testable a => Constraint -> Language -> (Tm Z -> a) -> Property
forAll0 c l = QC.forAllShrinkShow (genTm c l) (shrinkTm c) SC.pp

-- | Test a property on a term with a single free variable "x"
forAll1 :: Testable a => Constraint -> Language -> (Tm (S Z) -> a) -> Property
forAll1 c l = QC.forAllShrinkShow (genTm c l) (shrinkTm c) (SC.ppWith ("x" ::: VNil))

-- | Test a property on a term with two free variables "x" and "y"
forAll2 :: Testable a => Constraint -> Language -> (Tm (S (S Z)) -> a) -> Property
forAll2 c l = QC.forAllShrinkShow (genTm c l) (shrinkTm c) (SC.ppWith ("x" ::: "y" ::: VNil))

-- | Run all QuickCheck properties in this module.
testAll :: IO ()
testAll = do
    let args = QC.stdArgs { QC.maxSuccess = 1000 }
    putStrLn "prop_project_round_trip:"
    QC.quickCheckWith args (forAll0 Scoped Full SC.prop_project_round_trip)
    putStrLn "prop_parse_round_trip:"
    QC.quickCheckWith args (forAll0 Scoped Full SC.prop_parse_round_trip)
