module Tutorial.Lib where

import Data.Fin

import Prettyprinter (Doc, (<+>))
import Prettyprinter qualified as PP

import Text.ParserCombinators.Parsec.Error (ParseError)
import Text.ParserCombinators.Parsec.Pos (SourcePos, sourceColumn, sourceLine, sourceName)

import Test.QuickCheck

-- * Injection/Projection pairs

class Injection a b where
    inject :: a -> b 
class Injection b a => Projection a b where
    project :: a -> Maybe b

prop_Projection1 :: forall b a. (Arbitrary a, Eq a, Projection a b) => a -> Bool
prop_Projection1 a = case (project @a @b a) of 
                      Nothing -> True
                      Just b -> a == inject b

prop_Projection2 :: forall b a. (Arbitrary a, Eq a, Projection b a) => a -> Bool
prop_Projection2 a = project @b @a (inject a) == Just a

-- * Finite maps from Fin n

type Map a n = Fin n -> a

-- | the empty context has an empty domain
empty :: Map a Z
empty = \x -> case x of {}

-- | extend a map with a new definition, enlarging its domain
extend :: Map a n -> a -> Map a (S n)
extend g a = \x -> case x of { FZ -> a ; FS y -> g y }

-------------------------------------------------------------------------
-- * Display class for pretty printing with associated state, such as prececence

class Display s d where
    display :: d -> s -> Doc e

-- | Display the list of elements in parentheses,
-- punctuated by the given string.
-- (If there is only one element, don't include the parentheses)
multiple :: Display s a => String -> [a] -> s -> Doc e 
multiple s [x] = display x
multiple s xs =
   PP.parens . PP.sep <$>
       (PP.punctuate (PP.pretty s) <$> mapM display xs)

-------------------------------------------------------------------------
-- Display Instances for quoting, errors, source positions, names
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