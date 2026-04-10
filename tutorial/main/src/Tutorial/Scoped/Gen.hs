{-|
Module      : Tutorial.Scoped.Gen
Description : QuickCheck generators for well-scoped & well-typed lambda calculus terms

-}
module Tutorial.Scoped.Gen where

import Tutorial.Scoped.Syntax
import qualified Tutorial.Scoped.ScopeCheck as SC


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
tmId = Lam (bind (LocalName "x") (Var FZ))


-- For variables we need to know the number of variables in scope to 
-- be able to generate an arbitrary variable. 

--- >>> (Fin.universe :: [Fin N3])
-- [0,1,2]


-- | Generate a well-scoped pure lambda calculus term 
-- 
genScopedPureLC :: forall n. SNatI n => QC.Gen (Tm n)
genScopedPureLC = QC.sized go
    where
      -- At small size generate either a variable or "\x.x" depending on scope
      genBase :: forall n. SNat n -> Gen (Tm n) 
      genBase SZ = return tmId
      genBase SS = QC.elements (map Var Fin.universe)

      go :: forall n. SNatI n => Int -> QC.Gen (Tm n)
      go sz | sz <= 1 = genBase snat
      go sz = 
         let           
            -- generate a random name and increment the number of free variables
            gen1 = bind <$> genLocalName <*> go (sz - 1)

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
genTm Scoped PureLC = genScopedPureLC
genTm Scoped Full   = genScopedFull
genTm Typed  Full   = QC.sized genTypedFull
genTm Typed PureLC  = QC.sized genTypedPureLC

-- | shrink a term with 'n' free variables
shrinkTm :: SNatI n => Constraint -> Tm n -> [Tm n]
shrinkTm Scoped = shrinkScoped
shrinkTm Typed  = shrinkTyped

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
-- * Well-scoped generator for Full language
---------------------------------------------------------------------

-- For simplicity, this generator only generates "shallow" patterns
-- i.e. Match expressions where the pattern is either `()`, `(x,y)`
-- or `inj0 x`, or `inj1 y`.

genScopedFull :: forall n. SNatI n => QC.Gen (Tm n)
genScopedFull = QC.sized go
    where
      genBase :: forall n. SNat n -> Gen (Tm n) 
      genBase SZ = return Unit
      genBase SS = Var <$> QC.elements Fin.universe

      go :: forall n. SNatI n => Int -> QC.Gen (Tm n)
      go sz | sz <= 1 = genBase snat
      go sz = 
        let
          gen  = go (sz `div` 2)
          gen1 = bind <$> genLocalName <*> go (sz - 1)
            
          genMatch = do 
            e <- gen
            brs <- QC.oneof [genMatchUnit, genMatchPair, genMatchSum]
            return (Match e brs)

          genMatchUnit = do
            e' <- gen
            return [ Branch (bind PUnit e')]
          genMatchPair = do
            ln1  <- genLocalName
            ln2  <- genLocalName
            body <- go (sz - 1)
            return [ Branch (bind (PPair (PVar ln1) (PVar ln2)) body)]
          genMatchSum = do
            ln1 <- genLocalName
            ln2 <- genLocalName
            b1  <- go (sz `div` 2)
            b2  <- go (sz `div` 2)
            return [ Branch (bind (PInj 0 (PVar ln1)) b1)
                   , Branch (bind (PInj 1 (PVar ln2)) b2) ]

          gens = [ Lam <$> gen1,
                 App <$> gen <*> gen,
                 Pair <$> gen <*> gen,
                 Inj <$> QC.elements [0,1] <*> gen,
                 genMatch ]
        in
          QC.oneof (genBase snat : gens)           

---------------------------------------------------------------------
-- * Shrinking well-scoped terms
---------------------------------------------------------------------

-- | Shrink a well-scoped term, keeping it in the same scope @n@.
shrinkScoped :: SNatI n => Tm n -> [Tm n]
shrinkScoped (Lam t)  = 
    [ Lam (bind (getPat t) t') | t' <- shrinkScoped (getBody t) ]
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
-- * Pattern generation
---------------------------------------------------------------------

-- When generating a match expression, we want to generate a collection
-- of branches that are exhaustive and consistent. Each pattern should 
-- have the same type and all of them together should cover every potential 
-- value of that type. 

-- A pattern binding an unspecified number of variables together with the 
-- types of those variables. We need to hide m because each Pat in a list 
-- of exhaustive patterns may bind a different number of variables.
data SomePat where
    SomePat :: Pat m -> Vec m Ty -> SomePat

instance Show SomePat where
    show (SomePat p ctx) = SC.ppPat p

-- | generate a random list of exhaustive patterns for a given type
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

--- >>> QC.sample' (QC.sized (genPats (One :* One)))
-- [[w],[((), x)],[(y, y0)],[(v, ())],[((), ())],[((), x)],[v],[u],[(w, ())],[u],[(t, ())]]

---------------------------------------------------------------------
-- * Aux functions for well-typed generation
---------------------------------------------------------------------

-- | Generators for variables in scope of the correct type
-- NB: this list may be empty if there are no variables of the 
-- correct type in scope
genVars :: Vec n Ty -> Ty -> [ Gen (Tm n) ]
genVars vec ty = Vec.ifoldr (\ i ty' ans -> 
        if ty == ty' then return (Var i) : ans else ans) [] vec

-- | Generate a small value of the given type, in the given context
genVal :: forall n. Vec n Ty -> Ty -> Gen (Tm n)
genVal ctx ty = QC.oneof (gen : genVars ctx ty)
    where gen = case ty of
                 One -> pure Unit
                 (a :-> b) -> Lam <$> (bind <$> genLocalName
                                  <*> genVal (a ::: ctx) b)
                 (a :* b)  -> Pair <$> genVal ctx a <*> genVal ctx b
                 (a :+ b)  -> QC.oneof [Inj 0 <$> genVal ctx a, 
                                        Inj 1 <$> genVal ctx b ]

-- | Generate either a variable in scope of the correct type, or 
-- a minimal value of the correct type
genBase :: forall n. Vec n Ty -> Ty -> Gen (Tm n)
genBase ctx ty = 
    let vars = genVars ctx ty in
    if null vars then genVal ctx ty else QC.oneof vars

-- >>> QC.sample' (genBase (One ::: One ::: VNil) One)
-- [Var 1,Var 0,Unit,Var 0,Var 0,Var 1,Var 0,Var 0,Unit,Var 0,Var 0]

-- >>> QC.sample' (genBase VNil (One :-> One))
-- [Lam (bind y (Var 0)),Lam (bind s Unit),Lam (bind u (Var 0)),Lam (bind u (Var 0)),Lam (bind u Unit),Lam (bind y Unit),Lam (bind z Unit),Lam (bind t (Var 0)),Lam (bind z Unit),Lam (bind z Unit),Lam (bind s (Var 0))]

---------------------------------------------------------------------
-- * Well-typed term generator for full language
---------------------------------------------------------------------

-- | Generate a well-typed term 
genTypedFull :: forall n. SNatI n => Int -> QC.Gen (Tm n)
genTypedFull sz = do 
        ctx <- genCtx snat sz
        ty  <- genTy sz 
        go ctx ty sz 
    where 
        -- generate an arbitrary context
        genCtx :: forall n. SNat n -> Int -> QC.Gen (Vec n Ty)
        genCtx n sz = case snat_ n of
                        SZ_  -> pure VNil
                        SS_ m -> (:::) <$> genTy sz <*> genCtx m sz

        go :: forall n. Vec n Ty -> Ty -> Int -> QC.Gen (Tm n)
        go ctx ty sz | sz <= 1 = genBase ctx ty
        go ctx ty sz = 
          let
            gen ty' = go ctx ty' (sz `div` 2)

            -- introduction forms, selected by target type
            introGens = case ty of
              One       -> [ pure Unit ]
              (a :-> b) -> [ Lam <$> (bind <$> genLocalName
                                       <*> go (a ::: ctx) b (sz - 1)) ]
              (a :* b)  -> [ Pair <$> gen a <*> gen b ]
              (a :+ b)  -> [ Inj 0 <$> gen a, Inj 1 <$> gen b ]

            -- elimination forms, generate a randome type for 
            -- argument or scrutinee
            elimGens = 
                let appGen = do
                        a <- genTy (sz `div` 2)
                        App <$> gen (a :-> ty) <*> gen a

                    genBranch ty (SomePat p ctx2) = do
                        e <- go (ctx2 Vec.++ ctx) ty (sz `div` 2)
                        return (Branch (bind p e))

                    genMatch = do
                        a <- genTy (sz `div` 2) 
                        e <- gen a
                        ps <- genPats a (sz `div` 2)
                        brs <- mapM (genBranch ty) ps
                        return (Match e brs)

                in [ appGen, genMatch]
          in
            QC.oneof (genBase ctx ty : introGens ++ elimGens)


-- >>> QC.sample' (genTm Typed Full :: Gen (Tm (S Z)))
-- [Unit,Inj 1 Unit,Pair (Inj 1 (Var 0)) (Match Unit [Branch (bind (PVar v) (Lam (bind x (Var 2))))]),Match (Match (Var 0) [Branch (bind PUnit (Pair Unit (Var 0)))]) [Branch (bind (PPair (PVar v) PUnit) (Match (Var 0) [Branch (bind (PVar t) (Var 0))]))],Lam (bind x (Lam (bind y (Inj 1 Unit)))),Pair (Pair (Lam (bind s (Var 1))) (Var 0)) (Pair (Lam (bind x Unit)) (Pair Unit (Var 0))),Pair Unit (App (App (Lam (bind t (Lam (bind u (Lam (bind u (Lam (bind z (Var 3))))))))) Unit) (Match Unit [Branch (bind (PVar t) (Inj 1 (Var 0)))])),Match (App (Lam (bind u (App (Lam (bind s (Pair (Var 0) (Pair Unit (Var 0))))) Unit))) (Lam (bind s (Var 0)))) [Branch (bind (PPair PUnit (PPair PUnit (PVar v))) (Inj 1 (Pair (Inj 0 Unit) (Lam (bind z Unit)))))],App (Lam (bind x (Lam (bind w (Inj 1 (Pair (Pair Unit Unit) (Lam (bind z (Var 2))))))))) (App (Lam (bind v Unit)) (Lam (bind z (App (Var 0) Unit)))),App (Match (Match (App (Lam (bind t (Var 0))) (Var 0)) [Branch (bind (PVar t) (Match (Var 1) [Branch (bind (PVar u) (Lam (bind y (Var 0))))]))]) [Branch (bind (PVar t) (App (App (Lam (bind x (Lam (bind z (Lam (bind t (Inj 1 Unit))))))) (Var 1)) (Match (Var 1) [Branch (bind PUnit (Pair (Var 1) (Var 1)))])))]) (Var 0),Match Unit [Branch (bind (PVar u) (Pair (Lam (bind y (Lam (bind u (Inj 0 (Var 2)))))) (Lam (bind t (Lam (bind w (Var 2)))))))]]


---------------------------------------------------------------------
-- * Well-typed term generator for PureLC
---------------------------------------------------------------------

-- | generate a type in the pure lambda calculus + Unit
genTyPureLC :: Int -> QC.Gen Ty
genTyPureLC sz 
  | sz <= 1   = return One 
  | otherwise = QC.oneof [ return One, genArr ] 
     where   
       sz' = sz `div` 2
       genArr = (:->) <$> genTyPureLC sz' <*> genTyPureLC sz'


-- | generate a term in the pure lambda calculus
genTypedPureLC :: forall n. SNatI n => Int -> QC.Gen (Tm n)
genTypedPureLC sz = do
        ty <- genTyPureLC sz
        ctx <- genCtx snat sz
        go ctx ty sz
    where 
        genCtx :: forall n. SNat n -> Int -> QC.Gen (Vec n Ty)
        genCtx n sz = case snat_ n of
                     SZ_  -> pure VNil
                     SS_ m -> (:::) <$> genTyPureLC sz <*> genCtx m sz

        go :: forall n. Vec n Ty -> Ty -> Int -> QC.Gen (Tm n)
        go ctx ty sz | sz <= 1 = genBase ctx ty
        go ctx ty sz = 
          let
            gen ty' = go ctx ty' (sz `div` 2)

            -- Introduction forms, selected by target type
            introGens = case ty of
              One       -> [ pure Unit ]
              (a :-> b) -> [ Lam <$> (bind <$> genLocalName
                                       <*> go (a ::: ctx) b (sz - 1)) ]
              _  -> error $ "Not a PureLC type: " ++ show ty

            -- elimination forms, generate a random type for application
            elimGens = 
                let appGen = do
                        a <- genTyPureLC (sz `div` 2)
                        App <$> gen (a :-> ty) <*> gen a

                in [ appGen ]
          in
            QC.oneof (genBase ctx ty : introGens ++ elimGens)



---------------------------------------------------------------------
-- * Shrink well-typed terms
---------------------------------------------------------------------

-- | Shrink a well-typed term, keeping it in the same scope @n@.
-- If the input is well-typed, then the output will be well-typed, but not necessarily
-- with the same type
shrinkTyped :: SNatI n => Tm n -> [Tm n]
shrinkTyped = shrink 
  where
    shrink :: SNatI n => Tm n -> [Tm n]
    shrink (Lam t)    = [Lam (bind (getPat t) t') | t' <- shrink (getBody t)]
    shrink (App a b)  = [a,b] 
    shrink (Pair a b) = [a,b] ++ shrinkTwo Pair a b 
    shrink (Inj i a)  = [a] ++ [Inj i a' | a' <- shrink a]
    shrink (Match e _) = [e]
    shrink _ = []
   
    shrinkTwo f a b =
            [ f a' b | a' <- shrink a] ++ [ f a b' | b' <- shrink b]

---------------------------------------------------------------------
-- * QC helpers
---------------------------------------------------------------------

-- | Test a property on a closed term
forAll0 :: Testable a => Constraint -> Language -> (Tm Z -> a) -> Property
forAll0 c l = QC.forAllShrinkShow (genTm c l) (shrinkTm c) SC.pp

-- | Test a property on a term with a single free variable "x"
forAll1 :: Testable a => Constraint -> Language -> (Tm (S Z) -> a) -> Property
forAll1 c l = QC.forAllShrinkShow (genTm c l) (shrinkTm c) (SC.ppWith ("x" ::: VNil))

-- | Test a property on a term with two free variables "x" and "y"
forAll2 :: Testable a => Constraint -> Language -> (Tm (S (S Z)) -> a) -> Property
forAll2 c l = QC.forAllShrinkShow (genTm c l) (shrinkTm c) (SC.ppWith ("x" ::: "y" ::: VNil))

---------------------------------------------------------------------
-- * QC invocation
---------------------------------------------------------------------

-- | Run round-trip properties for parse/pp
testAll :: IO ()
testAll = do
    let args = QC.stdArgs { QC.maxSuccess = 1000 }
    putStrLn "prop_project_round_trip:"
    QC.quickCheckWith args (forAll0 Scoped Full SC.prop_project_round_trip)
    putStrLn "prop_parse_round_trip:"
    QC.quickCheckWith args (forAll0 Scoped Full SC.prop_parse_round_trip)
