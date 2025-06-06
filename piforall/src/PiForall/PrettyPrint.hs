-- | A Pretty Printer.
module PiForall.PrettyPrint
  ( Display (..),
    SourcePos,
    PP.Doc,
    pp,
    disp,
    DispInfo,
    initDI,
  )
where

import PiForall.ConcreteSyntax
import Control.Monad.Reader (MonadReader (ask, local), asks)
import Data.Fin qualified as Fin
import Data.Foldable qualified as Foldable
import Data.List as List
import Data.LocalName (LocalName)
import Data.LocalName qualified as LocalName
import Data.Map qualified as Map
import Data.Set qualified as S
import Prettyprinter (Doc, (<+>))
import Prettyprinter qualified as PP
import Text.ParserCombinators.Parsec.Error (ParseError)
import Text.ParserCombinators.Parsec.Pos (SourcePos, sourceColumn, sourceLine, sourceName)

-------------------------------------------------------------------------
-- Classes and Types for Pretty Printing
-------------------------------------------------------------------------

-- | The 'Display' class governs all types which can be turned into 'Doc's The
-- `disp` function is the main entry point for the pretty printer. Note that
-- 'Display' instances are only available for the "unscoped" representation of
-- the language; see 'ScopeCheck' ('unscope' more specifically) to transform a
-- scoped representation into an unscoped one for pretty-printing.
class Display d where
  display :: d -> DispInfo -> Doc e

-- | Convenience entry point for the pretty printer
pp :: (Display d) => d -> String
pp p = show (display p initDI)

disp :: (Display d) => d -> Doc e
disp x = display x initDI

-- | For debugging
-- debug :: (Display d) => d -> String
-- debug p = show (display p debugDI)
--   where
--     debugDI = initDI {showLongNames = True, showAnnots = True}

-- | The data structure for information about the display
data DispInfo = DI
  { -- | should we show type annotations?
    showAnnots :: Bool,
    -- | names that have been used
    dispAvoid :: S.Set GlobalName,
    -- | names currently in the local scope
    -- localNames :: [LocalName],
    -- | current precedence level
    prec :: Int,
    showLongNames :: Bool
  }

-- TODO: should we print internally-generated names, or user-friendly versions?

initDI :: DispInfo
initDI =
  DI
    { showAnnots = False,
      dispAvoid = S.empty,
      -- localNames = [],
      prec = 0,
      showLongNames = False
    }

-------------------------------------------------------------------------
-- Display Instances for quoting, errors, source positions, names
-------------------------------------------------------------------------

instance Display ParseError where
  display ps di = PP.pretty (show ps)

instance Display SourcePos where
  display p di =
    PP.pretty (sourceName p)
      PP.<> PP.colon
      PP.<> PP.pretty (sourceLine p)
      PP.<> PP.colon
      PP.<> PP.pretty (sourceColumn p)
      PP.<> PP.colon

------------------------------------------------------------------------
-- Display Instances for Modules
-------------------------------------------------------------------------

instance Display Module where
  display m = do
    dn <- display (moduleName m)
    di <- mapM display (moduleImports m)
    de <- mapM display (moduleEntries m)
    pure $
      PP.vcat $
        [PP.pretty "module" <+> dn <+> PP.pretty "where"]
          ++ di
          ++ de

instance Display ModuleImport where
  display (ModuleImport i) = pure $ PP.pretty "import" <+> disp i

instance Display [ModuleEntry] where
  display ds = do
    dd <- mapM display ds
    pure $ PP.vcat dd

instance Display ModuleEntry where
  display (ModuleDef n term) = do
    dn <- display n
    dt <- display term
    pure $ dn <+> PP.pretty "=" <+> dt
  display (ModuleDecl n ty) = do
    dn <- display n
    dt <- display ty
    pure $ dn <+> PP.pretty ":" <+> dt
  display (ModuleData n dataDef) = do
    dn <- display n
    dd <- display dataDef
    pure $ PP.pretty "data" <+> dn <+> dd
  display (ModuleFail failing) = do
    df <- display failing
    pure $ PP.pretty "fail" <+> df

instance Display DataDef where
  display (DataDef params sort constructors) = do
    dp <- display params
    ds <- display sort
    dc <- mapM display constructors
    pure $
      PP.nest
        2
        ( PP.vcat
            ( dp
                <+> PP.colon
                <+> ds
                <+> PP.pretty "where"
                : dc
            )
        )

instance Display ConstructorDef where
  display (ConstructorDef _ c (Telescope [])) = do
    pure $ PP.pretty c
  display (ConstructorDef _ c tele) = do
    dc <- display c
    dt <- display tele
    pure $ dc <+> PP.pretty "of" <+> dt

instance Display Telescope where
  display (Telescope t) = iter t
    where
      iter [] = mempty
      iter ((EntryDecl x tm) : tele) = do
        dtm <- display tm
        dtele <- iter tele
        return $
          PP.parens
            ( if x /= LocalName.internalName
                then PP.pretty (show x) <+> PP.colon <+> dtm
                else dtm
            )
            <+> dtele
      iter ((EntryDef x tm) : tele) = do
        dx <- display (Var x)
        dtm <- display tm
        dtele <- iter tele
        return $ PP.brackets (dx <+> PP.equals <+> dtm) <+> dtele

-------------------------------------------------------------------------
-- Disp Instances for Prelude types
-------------------------------------------------------------------------

displayMaybe :: (t -> DispInfo -> Doc d) -> Maybe t -> DispInfo -> Doc d
displayMaybe display m di = case m of
  (Just a) -> PP.pretty "Just" <+> display a di
  Nothing -> PP.pretty "Nothing"

instance (Display a) => Display (Maybe a) where
  display = displayMaybe display

displayEither ::
  (Display a, Display b) =>
  (forall a. (Display a) => a -> DispInfo -> Doc d) ->
  Either a b ->
  DispInfo ->
  Doc d
displayEither disp e di = case e of
  (Left a) -> PP.pretty "Left" <+> disp a di
  (Right a) -> PP.pretty "Right" <+> disp a di

instance (Display a, Display b) => Display (Either a b) where
  display = displayEither display

-------------------------------------------------------------------------

-- * Display instances for Prelude types used in AST

-------------------------------------------------------------------------

instance Display String where
  display = return . PP.pretty

instance Display Int where
  display = return . PP.pretty . show

instance Display Integer where
  display = return . PP.pretty . show

instance Display Double where
  display = return . PP.pretty . show

instance Display Float where
  display = return . PP.pretty . show

instance Display Char where
  display = return . PP.pretty . show

instance Display Bool where
  display = return . PP.pretty . show

-------------------------------------------------------------------------

-- * Display instances for Terms

-------------------------------------------------------------------------

levelApp :: Int
levelApp = 10

levelIf :: Int
levelIf = 0

levelLet :: Int
levelLet = 0

levelCase :: Int
levelCase = 0

levelLam :: Int
levelLam = 0

levelPi :: Int
levelPi = 0

levelSigma :: Int
levelSigma = 0

levelProd :: Int
levelProd = 0

levelArrow :: Int
levelArrow = 5

withPrec :: (MonadReader DispInfo m) => Int -> m a -> m a
withPrec p = local (\d -> d {prec = p})

parens :: Bool -> Doc d -> Doc d
parens b = if b then PP.parens else id

brackets :: Bool -> Doc d -> Doc d
brackets b = if b then PP.brackets else id

nthOpt :: [a] -> Int -> Maybe a
nthOpt (x : xs) 0 = Just x
nthOpt (x : xs) n = nthOpt xs (n - 1)
nthOpt [] _ = Nothing

instance Display Term where
  display TyType = return $ PP.pretty "Type"
  display (Global x) = return $ PP.pretty x
  display (Var n) = display n
  display a@(Lam _ _) = do
    n <- ask prec
    (binds, body) <- withPrec levelLam $ gatherBinders a
    return $ parens (levelLam < n) $ (PP.pretty "\\" PP.<> PP.sep binds PP.<> PP.pretty ".") <+> PP.nest 2 body
  display (App f x) = do
    n <- ask prec
    df <- withPrec levelApp (display f)
    dx <- withPrec (levelApp + 1) (display x)
    return $ parens (levelApp < n) $ df <+> dx
  display (Pi a n b) = do
    p <- ask prec
    lhs <- do
      -- if Fin.f0 `appearsFree` b
      --   then do
      dn <- display n
      da <- withPrec 0 (display a)
      return $ PP.parens (dn <+> PP.colon <+> da)
    -- else do
    --   withPrec (levelArrow + 1) (display a)
    db <- withPrec levelPi (display b)
    return $ parens (levelArrow < p) $ lhs <+> PP.pretty "->" <+> db
  display (Ann a b) = do
    sa <- ask showAnnots
    if sa
      then do
        da <- withPrec 0 (display a)
        db <- withPrec 0 (display b)
        return $ PP.parens (da <+> PP.pretty ":" <+> db)
      else display a
  display (Pos _ e) = display e
  display (TyCon "(=)" [a, b]) = do
    da <- withPrec 0 (display a)
    db <- withPrec 0 (display b)
    return $ PP.parens (da <+> PP.pretty "=" <+> db)
  display (TyCon "Sigma" [tyA, Lam x tyB]) = do
    -- if Fin.f0 `appearsFree` tyB
    --   then do
    dx <- display x
    dA <- withPrec 0 $ display tyA
    dB <- withPrec 0 $ display tyB
    return $
      PP.pretty "{"
        <+> dx
        <+> PP.pretty ":"
        <+> dA
        <+> PP.pretty "|"
        <+> dB
        <+> PP.pretty "}"
  -- else do
  --   p <- ask prec
  --   dA <- withPrec levelSigma $ display tyA
  --   dB <- withPrec levelSigma $ display tyB
  --   return $ parens (levelSigma < p) (dA PP.<+> PP.pretty "*" PP.<+> dB)
  display (DataCon "," [a, b]) = do
    p <- ask prec
    da <- withPrec levelProd $ display a
    db <- withPrec levelProd $ display b
    return $ parens (levelProd < p) (da PP.<> PP.pretty "," PP.<> db)
  display (Let x a b) = do
    p <- ask prec
    da <- display a
    dx <- display x
    db <- display b
    return $
      parens (levelLet < p) $
        PP.sep
          [ PP.pretty "let"
              <+> dx
              <+> PP.pretty "="
              <+> da
              <+> PP.pretty "in",
            db
          ]
  display t
    | Just i <- isNumeral t = display i
  display (TyCon n args) = do
    p <- ask prec
    dn <- display n
    dargs <- withPrec (levelApp + 1) $ mapM display args
    return $
      parens (levelApp < p && not (null args)) (PP.hsep (dn : dargs))
  display (DataCon n args) = do
    p <- ask prec
    dn <- display n
    dargs <- withPrec (levelApp + 1) $ mapM display args
    return $
      parens (levelApp < p && not (null args)) (PP.hsep (dn : dargs))
  display (Case scrut alts) = do
    p <- asks prec
    dscrut <- withPrec (levelCase + 1) $ display scrut
    dalts <- withPrec 0 $ mapM display alts
    return $
      parens (levelCase < p) $
        prettyCase dscrut dalts
  display (Subst a b) = do
    p <- asks prec
    da <- withPrec 0 $ display a
    db <- withPrec 0 $ display b
    return $
      parens (levelPi < p) $
        PP.sep
          [ PP.pretty "subst" <+> da,
            PP.pretty "by" <+> db
          ]
  display (TyEq a b) = do
    p <- ask prec
    da <- withPrec (levelApp + 1) $ display a
    db <- withPrec (levelApp + 1) $ display b
    return $ PP.parens $ (da <+> PP.pretty "=" <+> db)
  display TmRefl = do
    return $ PP.pretty "Refl"
  display (Contra ty) = do
    p <- ask prec
    dty <- display ty
    return $ parens (levelPi < p) $ PP.pretty "contra" <+> dty
  display TrustMe = return $ PP.pretty "TRUSTME"
  display PrintMe = return $ PP.pretty "PRINTME"

open = PP.flatAlt PP.emptyDoc (PP.pretty "{ ")

close = PP.flatAlt PP.emptyDoc (PP.pretty " }")

separator = PP.flatAlt PP.emptyDoc (PP.pretty "; ")

prettyCase :: Doc ann -> [Doc ann] -> Doc ann
prettyCase scrut xs =
  let top = PP.pretty "case" <+> scrut <+> PP.pretty "of"
   in if null xs
        then top <+> PP.pretty "{ }"
        else PP.nest 2 (top <> PP.hardline <> PP.vsep xs)

instance Display Match where
  display (Branch pat bd) = do
    dpat <- display pat
    dubd <- display bd
    return $ dpat <+> PP.pretty "->" <+> PP.align dubd

instance Display Pattern where
  display (PatCon c []) = display c
  display (PatCon c args) = do
    p <- ask prec
    dc <- display c
    dargs <- withPrec (levelApp + 1) $ display args
    return $
      parens
        (levelApp < p && iscons args)
        (PP.hsep [dc, dargs])
    where
      iscons [] = False
      iscons (_ : _) = True
  display (PatVar x) = display x

instance Display [Pattern] where
  display [] = mempty
  display (p : ps) = do
    da <- display p
    ds <- display ps
    return $ da <+> ds

instance Display LocalName where
  display l _ = PP.pretty (show l)

-------------------------------------------------------------------------

-- * Helper functions for displaying terms

-------------------------------------------------------------------------

gatherBinders :: Term -> DispInfo -> ([Doc d], Doc d)
gatherBinders (Lam n body) = do
  dn <- display n
  (rest, body') <- gatherBinders body
  return (dn : rest, body')
gatherBinders body = do
  db <- display body
  return ([], db)

-- displayFoldable :: Foldable f => String -> f Term -> DispInfo -> Doc e
-- displayFoldable j t = do
--   let il :: [(Int, Term)] = zip (iterate (1 +) 0) $ Foldable.toList t
--   dl <-
--     mapM
--       ( \(i, t) -> do
--           di <- display i
--           dt <- display t
--           return $ di <+> PP.pretty j <+> dt
--       )
--       il
--   return $ PP.vcat dl