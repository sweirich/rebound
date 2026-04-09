{-|
Module      : Named.PP
Description : Pretty printer for named syntax
Copyright   : (c) Stephanie Weirich, 2026
License     : MIT
Maintainer  : sweirich@seas.upenn.edu
Stability   : experimental

A module to display named syntax terms nicely. 

This pretty printer is built using the `Prettyprinter` 
library, which includes a number of definitions for 
turning data into `Doc`

-}
module Tutorial.Named.PP where

import Prettyprinter (Doc, (<+>))
import Prettyprinter qualified as PP
import Control.Monad.Reader ( MonadReader(local), asks )

import Tutorial.Named.Syntax

import Text.Parsec (ParseError, 
   SourcePos, sourceColumn, sourceLine, sourceName)


-- | Pretty-print on a single line (using 'PP.group' to collapse line breaks)
oneline :: Display DispState a => a -> String
oneline x = show (PP.group (display x initState))

-- | Pretty-print with possible line breaks
pp :: Display DispState a => a -> String
pp x = show (display x initState)

-- | For testing: run the pretty printer
test :: Display DispState a => a -> Doc e
test x = display x initState

-------------------------------------------------------------------------
-- * Display class for pretty printing with associated state, such as prececence

class Display s d where
    display :: d -> s -> Doc e

------------------------------------------------
-- * Pretty printing parameters and state
--
-- This simple pretty printer includes one piece of 
-- state that is maintained during conversion -- the 
-- current precedence level. This level controls where 
-- parentheses can be omitted from the output.
-- There is also one parameter to prettyprinting, which
-- controls the formatting of syntactic sugar. Do we want
-- to see things printed in a more mathematical style?
-- Or in a more programming language style?

-- | Parameters and state for pretty printing
data DispState = DI {
    -- | printing style
    style :: Style, 
    -- | precedence level
    prec  :: Int,
    -- | display with syntactic sugar
    sugar :: Bool,
    -- | unicode symbols
    unicode :: Bool
}

-- | Printing style controls how type names are displayed
data Style
    -- | Use @0@, @1@, @2@ for type names
    = Math
    -- | Use @Void@, @Unit@, @Bool@ for type names
    | Lang

initState :: DispState
initState = DI { style = Math, prec = levelBase, sugar = False, unicode=False }

------------------------------------------------
-- * precedence

-- | If the precedence of the current form (level)
-- is less than the precedence of the context (prec s)
-- add parentheses.
parens :: Int -> Doc d -> DispState -> Doc d
parens level d s = 
    if (level < prec s) then PP.parens d else d

-- | Most syntactic forms have precedence level 0
levelBase :: Int
levelBase = 0

levelBranch :: Int
levelBranch = 5

levelApp :: Int
levelApp = 10

withPrec :: (MonadReader DispState m) => Int -> m a -> m a
withPrec p = local (\d -> d {prec = p})

display0 :: Display DispState a => a -> DispState -> Doc e
display0 = withPrec 0 . display


-- | Display the list of elements in parentheses,
-- punctuated by the given string.
-- (If there is only one element, don't include the parentheses)
multiple :: Display s a => String -> [a] -> s -> Doc e 
multiple s [x] = display x
multiple s xs =
   PP.parens . PP.sep <$>
       (PP.punctuate (PP.pretty s) <$> mapM display xs)


------------------------------------------------
-- * Display instance for types

-- | display the unit type
dunit :: DispState -> Doc e
dunit s = 
    case style s of 
       Math -> PP.pretty "1"
       Lang -> PP.pretty "Unit"

-- | display the void type
dvoid :: DispState -> Doc e 
dvoid s = 
  case style s of 
     Math -> PP.pretty "0"
     Lang -> PP.pretty "Void"

-- | display the bool type
dbool :: DispState -> Doc e 
dbool s = 
  case style s of 
     Math -> PP.pretty "2"
     Lang -> PP.pretty "Bool"

instance Display DispState Ty where
    display (Prod []) = dunit
    display (Prod xs) = multiple " *" xs
       
    display (Sum []) = dvoid
    display (Sum [Prod [], Prod []]) = dbool
    display (Sum xs) = multiple " +" xs
    
    display (t1 :-> t2) = do
      s1 <- withPrec 1 (display t1)
      s2 <- withPrec 0 (display t2)
      parens 0 (s1 <+> PP.pretty "->" <+> s2)


-- >>> test (Sum [Prod[unitTy,voidTy],voidTy] :-> (boolTy :-> unitTy))
-- ((1 * 0) + 0) -> 2 -> 1

-- >>> test ((voidTy :-> voidTy) :-> voidTy :-> unitTy)
-- (0 -> 0) -> 0 -> 1

----------------------------------------------
-- * Diplay instance for Terms 

-- | Pretty-print a single case branch @p -> e@
displayBr :: (Tm,Tm) -> DispState -> Doc e
displayBr (p,e) = do
    s1 <- withPrec 0 (display p)
    s2 <- withPrec levelBranch (display e)
    return (s1 <+> PP.pretty "->" <+> s2)

-- | Pretty-print a list of case branches, adding @|@ separators when there are multiple
displayBrs :: [(Tm,Tm)] -> DispState -> [Doc e]
displayBrs []  s    = [PP.braces (PP.pretty "")]
displayBrs [x] s    = [displayBr x s]
displayBrs xs s =
    map (\b -> PP.pretty "|" <+> displayBr b s) xs

-- | Collect consecutive lambda binders so they can be printed as @λ x y z. e@
gatherBinders :: Tm -> ([String], Tm)
gatherBinders (Lam x e) = ((x:rest),e')
  where (rest,e') = gatherBinders e
gatherBinders e = ([],e)


instance Display DispState Tm where
    display (Var x)   = pure $ PP.pretty x
    display (Lam x e) = do
        s <- withPrec 0 (display e')
        showUnicode <- unicode
        let lambda = if showUnicode then PP.pretty "λ" else PP.pretty "\\" 
        parens 0 (lambda <+> PP.hsep (map PP.pretty (x:ys)) 
                              <> PP.dot <+> s)
           where (ys,e') = gatherBinders e
    display (Pair []) = pure $ PP.pretty "()"
    display (Pair es) = multiple "," es
    display (Inj 0 (Pair [])) = pure (PP.pretty "False")
    display (Inj 1 (Pair [])) = pure (PP.pretty "True")
    display (Inj i e) = do
        s <- withPrec (levelApp + 1) (display e)
        parens 0 (PP.pretty "inj" <> PP.pretty i <+> s)

    
    display (App e1 e2) = do
        useSugar <- asks sugar
        case e1 of
          Lam x b | useSugar -> do
            -- syntactic sugar for let
            s1 <- withPrec 0 (display b)
            s2 <- withPrec 0 (display e2)
            parens 0 (PP.pretty "let" <+> PP.pretty x <+> PP.equals <+> s2
                  <+> PP.pretty "in" <+> s1)
          _ -> do
            s1 <- withPrec levelApp (display e1)
            s2 <- withPrec (levelApp+1) (display e2)
            parens levelApp (s1 <+> s2)
        

    display (Case e brs) = do
        useSugar <- asks sugar
        case brs of
          -- syntactic sugar for if
          [(Inj 0 (Pair []), e1), 
           (Inj 1 (Pair []), e2)] | useSugar -> do
             s0 <- withPrec 0 (display e)
             s1 <- withPrec 0 (display e1)
             s2 <- withPrec 0 (display e2)
             parens 0 
                (PP.pretty "if" <+> s0 <+> PP.pretty "then" <+> s1
                  <+> PP.pretty "else" <+> s2)
          -- syntactic sugar for "e1 ; e2"
          [(Pair [], e2)] | useSugar -> do
             s1 <- withPrec 1 (display e)
             s2 <- withPrec 0 (display e2)
             parens 0
                (s1 <> PP.semi <+> s2)
          -- all case
          _ -> do           
            s1 <- withPrec 0 (display e)
            s2 <- withPrec 0 (displayBrs brs)
            parens 0
              (PP.hang 2 (PP.vsep 
                (PP.pretty "case" <+> s1 <+> PP.pretty "of" : s2)))

    display (Ann e t) = do
      s1 <- withPrec 0 (display e)
      s2 <- withPrec 0 (display t)
      parens 0 (s1 <+> PP.pretty ":" <+> s2)


-- >>> test (App (Var "x") (App (Var "x") (Var "x")))
-- x (x x)

-- >>> test (App (Var "x") (App (Var "x") (App  (Var "x") (Var "x"))))
-- x (x (x x))

-- >>> test (App (App (App (Var "x") (Var "x")) (Var "x")) (Var "x"))
-- x x x x

-- >>> test (App (Var "x") (Inj 0 (Var "y")))
-- x (inj0 y)

-- >>> test (App (Lam "x" (Var "x")) unitTm)
-- let x = () in x

-- >>> test (App (Lam "x" (Var "x")) (Lam "y" (Var "y")))
-- let x = λ y. y in x

tm = Case (Case (Inj 1 unitTm) [(Inj 0 unitTm, unitTm),
                                      (Inj 1 unitTm, Var "x")]) [(unitTm,unitTm)]
-- >>> test tm                                      
-- (if True then () else x); ()

example :: Tm
example = (Case (Var "x") [(Inj 0 (Pair [Var "y", Var "z"]), (App (Var "y") (Var "y"))),
                           (Inj 1 (Var "z"), (App (Var "z") (Var "z")))])
-- >>> test example
-- case x of
--   | inj0 (y, z) -> y y
--   | inj1 z -> z z

-- >>> test (App example (Var "w"))
-- (case x of
--    | inj0 (y, z) -> y y
--    | inj1 z -> z z) w

-- >>> test (App (Var "w") example)
-- w (case x of
--      | inj0 (y, z) -> y y
--      | inj1 z -> z z)

-- >>> test (App (Lam "x" (Lam "y" (Var "x"))) example)
-- let x = case x of
--           | inj0 (y, z) -> y y
--           | inj1 z -> z z in λ y. x


-- >>> test (seqTm unitTm unitTm)
-- case () of
--   () -> ()

-- >>> test (seqTm unitTm (seqTm unitTm unitTm))
-- case () of
--   () -> (case () of
--            () -> ())

-- >>> test (seqTm (seqTm unitTm unitTm) unitTm)
-- case case () of
--        () -> () of
--   () -> ()

-------------------------------------------------------------------------
-- Display Instances for errors and source positions
-------------------------------------------------------------------------


instance Display s ParseError where
  display ps di = PP.pretty (show ps)

instance Display s SourcePos where
  display p di =
    PP.pretty (sourceName p)
      PP.<> PP.colon
      PP.<> PP.pretty (sourceLine p)
      PP.<> PP.colon
      PP.<> PP.pretty (sourceColumn p)
      PP.<> PP.colon

-------------------------------------------------------------------------
-- Disp Instances for Prelude types
-------------------------------------------------------------------------

displayMaybe :: (t -> s -> Doc d) -> Maybe t -> s -> Doc d
displayMaybe display m di = case m of
  (Just a) -> PP.pretty "Just" <+> display a di
  Nothing -> PP.pretty "Nothing"

instance (Display s a) => Display s (Maybe a) where
  display = displayMaybe display

displayEither ::
  (Display s a, Display s b) =>
  (forall a. (Display s a) => a -> s -> Doc d) ->
  Either a b ->
  s ->
  Doc d
displayEither disp e di = case e of
  (Left a) -> PP.pretty "Left" <+> disp a di
  (Right a) -> PP.pretty "Right" <+> disp a di

instance (Display s a, Display s b) => Display s (Either a b) where
  display = displayEither display


instance Display s String where
  display = return . PP.pretty

instance Display s Int where
  display = return . PP.pretty . show

instance Display s Integer where
  display = return . PP.pretty . show

instance Display s Double where
  display = return . PP.pretty . show

instance Display s Float where
  display = return . PP.pretty . show

instance Display s Char where
  display = return . PP.pretty . show

instance Display s Bool where
  display = return . PP.pretty . show
