{- 

  Part 3: well-scoped de Bruijn indices in practice
          parsing, scope checking, pretting printing, random testing 


-}

module Tutorial.Talk3 where


import Test.QuickCheck
import Tutorial.Scoped.Syntax
import qualified Rebound.Bind.Pat as Pat
import Data.Vec ( (!) )
import Data.Maybe as Maybe
import Tutorial.Scoped.Gen
import Tutorial.Scoped.Eval
import Tutorial.Scoped.ScopeCheck


----------------------------------------------------------- 
-- ** Parsing, Scope Checking and printing
----------------------------------------------------------- 
{-

       parsing               scope checking
String ------> Named Syntax ----------------> Scoped Syntax


             injection              pretty printing
Scoped Syntax -------> Named Syntax -------------> String


-}



----------------------------------------------------------- 
-- Parsing and pretty printing closed terms
----------------------------------------------------------- 

Right tmId1 = parse "\\x.x"

-- >>> pp tmId1
-- "\\ x. x"


Right tmSwap = parse "\\x. case x of (y,z) -> (z,y)"


-- >>> pp tmSwap
-- "\\ x. case x of\n       (y, z) -> (z, y)"

-- >>> parse "\\x.y"
-- Left (ScopeError (UnboundVariable "y"))


----------------------------------------------------------- 
-- Parsing and pretty printing open terms
----------------------------------------------------------- 


names :: Vec N2 String
names = "y" ::: "z" ::: VNil


-- >>> parseWith names "\\x.z"
-- Right (Lam (bind x (Var 2)))

Right g = parseWith names "\\x.y"

-- >>> ppWith names g
-- "\\ x. y"



----------------------------------------------------------- 
-- QuickCheck and well-scoped/well-typed term generation 
----------------------------------------------------------- 

-- Tutorial.Scoped.Gen includes instances of QuickCheck's 
-- several generators/shrinkers for terms and patterns

-- Entry point:
-- >>> :t forAll0
-- forAll0 :: Testable a => Constraint -> Language -> (Tm 'Z -> a) -> Property


{-
Generate either well-scoped or well-typed terms
-- data Constraint = Scoped | Typed

Generate either terms from pure lambda calculus or full language
-- data Language = PureLC | Full

-}


----------------------------------------------------------- 
-- Using quickcheck
-----------------------------------------------------------  

-- evaluating twice returns the same result
prop_eval_idempotent :: Tm Z -> Property
prop_eval_idempotent = \t ->
    discardAfter 10000 $   -- skip if test runs too long
    case eval t of
        Just v ->
            counterexample ("v: " ++ pp v) $
            property (eval v == Just v)
        Nothing ->
            discard

{-
ghci> qc100k (forAll0 Scoped PureLC prop_eval_idempotent)

ghci> qc100k (forAll0 Scoped Full prop_eval_idempotent)

ghci> qc100k (forAll0 Typed Full prop_eval_idempotent)

-}

-- all terms produce values (NB: this holds for well-typed terms only!)
prop_eval_exists_Val :: Tm Z -> Property
prop_eval_exists_Val = \t ->
    within  10000 $   -- (within) tests fail for too many steps
    case eval t of
        Just v ->
            counterexample ("not a value: " ++ pp v) $
            property (isVal v)
        Nothing ->
            counterexample ("doesn't eval") $
            property False

{-
ghci> qc100k (forAll0 Scoped PureLC prop_eval_exists_Val)

ghci> qc100k (forAll0 Typed PureLC prop_eval_exists_Val)

ghci> qc100k (forAll0 Typed Full prop_eval_exists_Val)

-}


----------------------------------------------------------- 
-- But wait, there's more!
-----------------------------------------------------------

{-

-- Tutorial also includes scope-preserving CPS conversion example

-- Library repository includes examples
--     letrec, dependent pattern matching, etc.
--     HOAS wrapper, scope checking, System F, "Names for Free"

-- Large end-to-end example: pi-forall
--     
-- Paper includes discussion about the implementation and benchmarks


-}

----------------------------------------------------------- 
-- Related Work
-----------------------------------------------------------

{-

de Bruijn, Nameless dummies
Marcello Fiore's work on presheaves
McBride's dissertation, follow-on work
Autosubst library in Rocq (Stark et al.)

Bird and Patterson, de Bruijn indices as nested datatypes
Ed Kmett, "bound" library
Weirch and Yorgey, "unbound" library

-}



----------------------------------------------------------- 
-- Conclusion
-----------------------------------------------------------

{- 

-- Well-scoped de Bruijn indices are a well-scoped use 
-- of dependent types

-- Types ensure necessary weakening/substitutions happen 

-- Minimal requirements for "proofs"
--   GHC can automatically use nat lemmas when requested


-}
