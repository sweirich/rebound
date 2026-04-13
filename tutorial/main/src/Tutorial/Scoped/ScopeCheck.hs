{-|
Module      : Scoped.ScopeCheck
Description : Parser and Pretty Printer for scoped terms

-}
module Tutorial.Scoped.ScopeCheck (
  -- * Scope-check errors
  ScopeCheckError(..),
  -- * Conversions to named version of AST
  injectTy,
  projectTy,
  injectTmWith,
  injectTm,
  projectTmWith,
  projectTm,
  -- * Round-trip properties
  prop_project_round_trip,
  prop_parse_round_trip,
  -- * Unit tests
  unitTests,
  runUnitTests,
  -- * pretty printer for scoped representation
  pp,
  ppWith,
  ppPat,
  -- * parser for scoped representation
  Error(..),
  parse,
  parseWith
) where

import Test.QuickCheck
import Test.HUnit (Test(..), (~:), (~=?), runTestTT, Counts)

import Data.Fin
import Data.SNat
import Data.Vec (Vec(..), (!)) 
import qualified Data.Vec as Vec
import qualified Rebound as Rebound

import qualified Tutorial.Named.Syntax as N
import qualified Tutorial.Named.PP as N
import qualified Tutorial.Named.Parser as N
import qualified Tutorial.Scoped.Syntax as S

import Data.Type.Equality ((:~:)(Refl))

import Text.Parsec ( ParseError )

-- | Find the index of the first element that satisfies the given predicate
findIndex :: (a -> Bool) -> Vec n a -> Maybe (Fin n)
findIndex f VNil = Nothing
findIndex f (x ::: xs) = if f x then return FZ else FS <$> findIndex f xs


------------------------------------------------------------------------
-- * Parsing and Pretty Printing examples
------------------------------------------------------------------------

{-
       N.parse                 project
String ------> Named Syntax --------> Scoped Syntax

               inject                N.pp
Scoped Syntax -------> Named Syntax -------> String

-}


-- >>> N.parseTm "\\ x y. x"



-- >>> projectTm (N.Lam "x" (N.Lam "y" (N.Var "x")))




-- both steps at once.

-- >>> parse "λ x y. x"




-- Things can go wrong. 

-- >>> parse "λ x x"


-- >>> parse "λ y . x"



-- We want to work up to alpha-equivalence.

t1 :: S.Tm Z
t1 = case parse "λ x. x" of Right y -> y ; _ -> error "OOPS"
t2 :: S.Tm Z
t2 = case parse "λ y. y" of Right y -> y ; _ -> error "OOPS"

-- >>> t1 == t2


-- >>> t1


-- >>> t2


t3 :: S.Tm Z
t3 = case parse "λ x. λ y. x" of Right y -> y ; _ -> error "OOPS"
t4 :: S.Tm Z
t4 = case parse "λ x. λ y. y" of Right y -> y ; _ -> error "OOPS"

-- >>> t3 == t4



-- Pretty printing also goes through the named syntax

n1 :: N.Tm
n1 = injectTm t1
n2 :: N.Tm
n2 = injectTm t2

-- >>> t2


-- >>> n2



-- >>> N.pp n1




-- >>> pp t2



-- we keep the original names

-- >>> t2



-- >>> n2



-- >>> pp t3




-- freshen if there is shadowing

t5 :: S.Tm Z
t5 = case parse "λ x. λ x. x" of Right y -> y ; _ -> error "OOPS"

-- >>> t5


-- >>> pp t5




-- Can also parse and print *open* terms by providing additional information

-- >>> :t parseWith
-- parseWith :: [(String, Fin n)] -> String -> Either Error (Tm n)


-- >>> parseWith [("x", FZ)] "λ y. x"
-- Right (Lam (bind1 (Var 1)))



-- >>> :t ppWith
-- ppWith :: Vec n String -> Tm n -> String

-- >>> ppWith ("x" ::: VNil) (S.Lam (S.bind1 (S.LocalName "y") (S.Var f1)))





------------------------------------------------------------------------
-- * Parsing and Pretty Printing (top-level entry points)
------------------------------------------------------------------------

-- | Errors that can occur during scope-checking.
data ScopeCheckError
  = UnboundVariable String
    -- ^ A variable name was not found in the current scope.
  | UnsupportedInjection Int
    -- ^ An injection index other than 0 or 1 was encountered.
  | UnsupportedForm N.Tm
    -- ^ The term uses a syntactic form that has no scoped equivalent,
    --   e.g. a tuple of arity other than 0 or 2, or an unrecognised
    --   pattern in a case expression.
  deriving (Show, Eq)

-- | Top-level errors from 'parse' / 'parseWith'.
data Error = ScopeError ScopeCheckError | ParseError ParseError
  deriving (Show,Eq)

-- | Parse a closed term
parse :: String -> Either Error (S.Tm Z)
parse s = case N.parseTm s of
              Left pe  -> Left (ParseError pe)
              Right ne -> case projectTm ne of
                            Left err -> Left (ScopeError err)
                            Right se -> Right se

-- >>> parse "\\ x y. x"


-- >>> parse "λ y . x"


-- | Parse an open term
parseWith :: Vec n String -> String -> Either Error (S.Tm n)
parseWith vs s = case N.parseTm s of
              Left pe  -> Left (ParseError pe)
              Right ne -> case projectTmWith vs ne of
                            Left err -> Left (ScopeError err)
                            Right se -> Right se

-- | Pretty-print a closed term via the Named pretty printer
pp :: S.Tm Z -> String
pp = N.pp . injectTm

-- | Pretty-print an open term: requires names for the free variables
ppWith :: Vec n String -> S.Tm n -> String
ppWith e t = N.pp (injectTmWith e t)

-- | Pretty-print a pattern
ppPat :: S.Pat m -> String
ppPat p = N.pp (fst (injectPat p VNil))

------------------------------------------------------------------------
-- * Type conversions
------------------------------------------------------------------------

-- | Embed a simple binary type into the n-ary named type language.
-- Products become singleton @Prod@ lists and sums become singleton @Sum@ lists.
injectTy :: S.Ty -> N.Ty
injectTy = to where
    to (t1 S.:-> t2) = to t1 N.:-> to t2
    to S.One = N.unitTy
    to (t1 S.:* t2) = N.Prod [to t1, to t2]
    to (t1 S.:+ t2) = N.Sum [to t1, to t2]

-- | Project a named type back to a simple binary type.
-- Fails (@Nothing@) when the named type uses n-ary products or sums with
-- any arity other than 0 (unit) or 2 (binary product/sum).
projectTy :: N.Ty -> Maybe S.Ty
projectTy = to where
   to (t1 N.:-> t2) = (S.:->) <$> to t1 <*> to t2
   to (N.Prod []) = pure S.One
   to (N.Prod [t1,t2]) = (S.:*) <$> to t1 <*> to t2
   to (N.Prod _) = Nothing
   to (N.Sum [t1,t2]) = (S.:+) <$> to t1 <*> to t2
   to (N.Sum _) = Nothing

------------------------------------------------------------------------
-- * Term conversions
------------------------------------------------------------------------


-- | Return @s@ if it does not appear in the vector, otherwise try
-- @s0@, @s1@, @s2@, … until a fresh name is found.
-- >>> freshen "x" ("x" ::: VNil)
-- "x0"
-- >>> freshen "x" (show (S.LocalName "x") ::: VNil)
-- "x0"
freshen :: String -> Vec n String -> String
freshen s vs
    | not (inVec s vs) = s
    | otherwise        = go (0 :: Int)
  where
    go i | not (inVec (s ++ show i) vs) = s ++ show i
         | otherwise                    = go (i + 1)

inVec s vs = any (== s) vs

-- | Convert an open well-scoped term to a named term, given a vector of
-- names for the free variables.  The head of the vector (@index 'FZ'@) names
-- the innermost variable; names are prepended at each binder site.
injectTmWith :: Vec n String -> S.Tm n -> N.Tm
injectTmWith vs (S.Var x)     = N.Var (vs ! x)
injectTmWith vs (S.Lam t)     = N.Lam s (injectTmWith (s ::: vs) (S.getBody t))
                                  where s = freshen (show (S.getPat t)) vs
injectTmWith vs (S.App e1 e2) = N.App (injectTmWith vs e1) (injectTmWith vs e2)
injectTmWith vs (S.Unit)      = N.Pair []
injectTmWith vs (S.Pair e1 e2)= N.Pair [injectTmWith vs e1, injectTmWith vs e2]
injectTmWith vs (S.Inj i e)   = N.Inj i (injectTmWith vs e)
injectTmWith vs (S.Match e brs) =
    N.Case (injectTmWith vs e) (map (injectBranch vs) brs)

-- | Convert a closed well-scoped term to a named term.
-- Variable names are taken from the 'S.LocalName' hints stored in binders.
injectTm :: S.Tm Z -> N.Tm
injectTm = injectTmWith VNil

-- | Convert a scoped branch to a named (pattern, body) pair.
injectBranch :: Vec n String -> S.Branch n -> (N.Tm, N.Tm)
injectBranch vs (S.Branch b) =
    let (npat, vs') = injectPat (S.getPat b) vs
    in (npat, injectTmWith vs' (S.getBody b))

-- | Convert a scoped pattern to a named pattern, extending the name context
-- with fresh names for each bound variable.
injectPat :: forall m n. S.Pat m -> Vec n String -> (N.Tm, Vec (m + n) String)
injectPat (S.PVar ln) vs =
    let s = freshen (show ln) vs
    in (N.Var s, s ::: vs)
injectPat S.PUnit vs = (N.Pair [], vs)
injectPat (S.PPair (p1 :: S.Pat m1) (p2 :: S.Pat m2)) (vs :: Vec n String) =
    -- PPair p1 p2 :: Pat (m2 + m1); p2's vars are innermost (lower body indices).
    -- Process p1 first so its names sit deeper, then prepend p2's names on top.
    let (np1, vs1) = injectPat p1 vs
        (np2, vs2) = injectPat p2 vs1
    in case axiomAssoc @m2 @m1 @n of
         Refl -> (N.Pair [np1, np2], vs2)
injectPat (S.PInj i p) vs =
    let (np, vs') = injectPat p vs
    in (N.Inj i np, vs')



-- | Convert a named term to a closed well-scoped term.
-- Returns @Left err@ if the named term contains free variables or uses
-- syntactic forms not supported by the simple language (e.g. n-ary patterns).
projectTm :: N.Tm -> Either ScopeCheckError (S.Tm Z)
projectTm = projectTmWith VNil


-- | Convert a named term to a well-scoped term in scope @n@, given an
-- association list mapping in-scope variable names to their de Bruijn
-- indices.  Each binder prepends a new entry and shifts all existing
-- indices up by one.  Returns @Left err@ if a free variable is
-- encountered or if the term uses a syntactic form not supported by the
-- simple language (e.g. n-ary patterns).
projectTmWith :: Vec n String -> N.Tm -> Either ScopeCheckError (S.Tm n)
-- A variable must be in scope; fail with UnboundVariable if not found
projectTmWith vs (N.Var v) = case findIndex (==v) vs of
    Nothing -> Left (UnboundVariable v)
    Just x  -> Right (S.Var x)
-- λ-abstraction: extend the scope with the bound name
projectTmWith vs (N.Lam v b) = do
    b' <- projectTmWith (v ::: vs) b
    return $ S.Lam (S.bind (S.LocalName v) b')
projectTmWith vs (N.App f a) = do
    f' <- projectTmWith vs f
    a' <- projectTmWith vs a
    return $ S.App f' a'
-- Empty tuple () maps to Unit
projectTmWith vs (N.Pair []) = return $ S.Unit
-- Binary tuple maps to Pair
projectTmWith vs (N.Pair [e1,e2]) = 
    S.Pair <$> projectTmWith vs e1 <*> projectTmWith vs e2
-- Only injections 0 and 1 are supported
projectTmWith vs (N.Inj i e1)
    | i == 0 || i == 1 = S.Inj i <$> projectTmWith vs e1
    | otherwise        = Left (UnsupportedInjection i)
projectTmWith vs (N.Case e brs) = do
    a' <- projectTmWith vs e
    brs' <- mapM (projectBranchWith vs) brs
    return (S.Match a' brs')
projectTmWith vs t = Left (UnsupportedForm t)

-- | A projected pattern, binding an arbitrary number of names
-- The names are also listed in the length-indexed vector
data PatNames where
    PatNames :: S.Pat m -> Vec m String -> PatNames

projectPat :: N.Tm -> Either ScopeCheckError PatNames
projectPat (N.Var x) = return (PatNames (S.PVar (S.LocalName x)) (x ::: VNil))
projectPat (N.Inj i t) | i == 0 || i == 1 = do
    pn <- projectPat t 
    case pn of 
        PatNames p vs -> return (PatNames (S.PInj i p) vs)
projectPat (N.Pair [t1, t2]) = do
    p1 <- projectPat t1
    p2 <- projectPat t2
    case (p1,p2) of 
        (PatNames p1 vs1, PatNames p2 vs2) -> 
            return (PatNames (S.PPair p1 p2) (vs2 Vec.++ vs1))
projectPat (N.Pair []) = return (PatNames S.PUnit VNil)
projectPat t = Left (UnsupportedForm t)

projectBranchWith :: Vec n String -> (N.Tm,N.Tm) -> Either ScopeCheckError (S.Branch n)
projectBranchWith vs (t1, t2) = do
    pn <- projectPat t1
    case pn of 
        PatNames pat vs' -> do
            e <- projectTmWith (vs' Vec.++ vs) t2
            return (S.Branch (S.bind pat e))

------------------------------------------------------------------------
-- * Round-trip properties
------------------------------------------------------------------------

-- | Injecting a scoped term into named form and projecting back yields
-- the original term.
prop_project_round_trip :: S.Tm Z -> Bool
prop_project_round_trip i = 
   projectTm (injectTm i) == Right i

-- | Pretty-printing a term and parsing it back yields the original named term.
prop_parse_round_trip :: S.Tm Z -> Bool
prop_parse_round_trip i =
   parse (pp i) == Right i

------------------------------------------------------------------------
-- * Unit tests
------------------------------------------------------------------------

-- | Run all unit tests for this module.
runUnitTests :: IO ()
runUnitTests = runTestTT unitTests >>= print

-- | All unit tests for this module.
unitTests :: Test
unitTests = TestList
    [ freshenTests
    , parseTests
    , ppTests
    , tyTests
    ]

-- freshen

freshenTests :: Test
freshenTests = "freshen" ~: TestList
    [ "no conflict"        ~: freshen "x" VNil              ~=? "x"
    , "one conflict"       ~: freshen "x" ("x" ::: VNil)    ~=? "x0"
    , "skip x0"           ~: freshen "x" ("x" ::: "x0" ::: VNil) ~=? "x1"
    , "no conflict other"  ~: freshen "x" ("y" ::: VNil)    ~=? "x"
    ]

-- parse and pp (concrete cases)

parseTests :: Test
parseTests = "parse" ~: TestList
    [ "identity fn"    ~: parse "λ x. x"       ~=? 
        Right S.ex_id
    , "const fn"       ~: parse "λ x. λ y. x"  ~=? 
        Right S.ex_const
    , "shadowing"      ~: parse "λ x. λ x. x"  ~=? 
        Right (S.Lam (S.bind (S.LocalName "x") (S.Lam (S.bind (S.LocalName "x") (S.Var FZ)))))
    , "application"    ~: parse "λ f. λ x. f x" ~=? 
        Right (S.Lam (S.bind (S.LocalName "f") (S.Lam (S.bind (S.LocalName "x") 
            (S.App (S.Var f1) (S.Var f0))))))
    , "unbound var"    ~: parse "λ x. y" ~=? Left (ScopeError (UnboundVariable "y"))
    ]


ppTests :: Test
ppTests = "parse" ~: TestList
    [ "identity fn"    ~: pp S.ex_id ~=? "\\ x. x"
    , "const fn"       ~: pp S.ex_const ~=? "\\ x y. x"  
    , "shadowing"      ~: 
        pp (S.Lam (S.bind (S.LocalName "x") (S.Lam (S.bind (S.LocalName "x") (S.Var FZ)))))
        ~=? "\\ x x0. x0"
    , "application"    ~: 
        pp (S.Lam (S.bind (S.LocalName "f") (S.Lam (S.bind (S.LocalName "x") 
            (S.App (S.Var f1) (S.Var f0)))))) 
        ~=? "\\ f x. f x"
    ]

-- injectTy / projectTy round trips

tyTests :: Test
tyTests = "injectTy/projectTy" ~: TestList
    [ "One"     ~: projectTy (injectTy S.One)                  ~=? Just S.One
    , "arrow"   ~: projectTy (injectTy (S.One S.:-> S.One))    ~=? Just (S.One S.:-> S.One)
    , "product" ~: projectTy (injectTy (S.One S.:* S.One))     ~=? Just (S.One S.:* S.One)
    , "sum"     ~: projectTy (injectTy (S.One S.:+ S.One))     ~=? Just (S.One S.:+ S.One)
    ]
