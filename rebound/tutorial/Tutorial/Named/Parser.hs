-- | Parser for a small lambda calculus with n-ary products and sums.
-- It is implemented using the 'parsec' library and produces abstract
-- syntax represented by Named.Syntax
-- 
module Tutorial.Named.Parser where

import Control.Monad (void)
--import qualified Data.Functor.Identity

import Text.Parsec 
import qualified Text.Parsec.Token as P
import qualified Text.Parsec.Combinator as P
import Text.Parsec.Language (haskellStyle)
import Text.Parsec.Expr (Assoc (..), Operator (..), buildExpressionParser)


import Tutorial.Named.Syntax

{- Concrete syntax 

This is the concrete syntax for a small lambda calculus with n-ary 
products and sums. 


types 

   t ::= 
      | Unit
      | Void
      | t -> t            function type
      | t1 * .. * tn      product type
      | t1 + ... + tn     sum type
      | ( t )             parentheses

   -> is left associative 
   1 can also be used for Unit
   0 can also be used for Void
   Bool/2 is syntactic sugar for 1+1

terms

   e ::= x 
      | \ x1 . e          lambda expressions 
      | ()                unit
      | e1 , ..., en      product intro
      | inj i e           sum intro  
      | e1 e2             application
      | case e of brs     pattern match
      | e : t             annotation
      | ( e )             parentheses

      (syntactic sugar)
      | True | False | if e1 then e2 else e3
      | \x1 ... xn . e    
      | let x = e1 in e2 
   
   br ::= | p -> e        branch

   application is left associative
   lambda and match scope as far as possible
   can omit first '|' in list of branches

patterns

   p ::= x                variable
      | ()                unit 
      | (p1, ... , p2)    pair
      | inj i p           sum
      | (p : t)           annotation
      | (p)
      
-}

-----------------------------------------------------------
-- * Top-level

-- Parser type from 'Parsec'
type Parser a =
  Parsec
    String   -- The input is a sequence of Char
    ()       -- User state
    a        -- the type of the object being parsed


-- | Test a Parser on a String
testParser :: Parser t -> String -> Either ParseError t
testParser parser str =
    runParser (do whiteSpace; v <- parser; eof; return v) () "<interactive>" str

-- | Parse an expression
parseTm :: String -> Either ParseError Tm
parseTm = testParser tm

------------------------------------------------------------------
-- * Lexer

-- The tokenizer identifies the tokens in the language and consumes 
-- whitespace as appropriate. For this language, we start with a minimal
-- definition based on Haskell
-- + identifiers must start with lowercase letter or '_' and contain
--   only alphanumeric characters (plus '_') 
-- + operators start with a symbol
tokenizer :: P.TokenParser u 
tokenizer = P.makeTokenParser haskellStyle {
    P.reservedOpNames = ["*", "+", ",", "=", "\\", "|", "->", ";" ,"."], 
    P.reservedNames   = ["case","of","let","in","if","then","else", "λ", 
                         "True", "False", "Bool", "Void", "Unit", "Inj"] }

-- see the documentation in 
-- https://hackage.haskell.org/package/parsec-3.1.18.0/docs/Text-Parsec-Token.html
-- for these operations

identifier :: Parser String
identifier = P.identifier tokenizer

symbol :: String -> Parser String
symbol = P.symbol tokenizer

whiteSpace :: Parser ()
whiteSpace = P.whiteSpace tokenizer

lexeme :: Parser a -> Parser a
lexeme = P.lexeme tokenizer

colon, dot, comma :: Parser ()
colon = void (P.colon tokenizer)
dot = void (P.dot tokenizer)
comma = void (P.comma tokenizer)

parens, brackets, braces :: Parser a -> Parser a
parens = P.parens tokenizer
brackets = P.brackets tokenizer
braces = P.braces tokenizer

reserved, reservedOp :: String -> Parser ()
reserved = P.reserved tokenizer
reservedOp = P.reservedOp tokenizer

natural :: Parser Int
natural = do 
  x <- fromInteger <$> P.decimal tokenizer
  if x < 0 then fail "nonnegative number expected" else return x

-----------------------------------------------------------------
-- * Types

voidP :: Parser Ty 
voidP = (reserved "Void" <|> reserved "0") >> return voidTy

unitP :: Parser Ty
unitP = (reserved "Unit" <|> reserved "1") >> return unitTy

boolP :: Parser Ty
boolP = (reserved "Bool" <|> reserved "2") >> return boolTy

-- parse a sequence of types, separated by either '*' or '+'
-- once you see the operator, the list must continue to use the same operator
-- this definition is factored this way so that we don't need to backtrack 
-- after parsing the first element of the list
prodOrSumTy :: Parser Ty -> Parser Ty
prodOrSumTy p = do
   x <- p
   let seq op f = try (reservedOp op) >> do
         xs <- P.sepBy1 p (reservedOp op) 
         return $ f (x:xs)
   seq "*" Prod
     <|> seq "+" Sum
     <|> return x

-- >>> testParser (prodOrSumTy unitTy) "Unit * Unit * Unit"
-- Right (Prod [Prod [],Prod [],Prod []])

-- >>> testParser (prodOrSumTy unitTy) "Unit"
-- Right (Prod [])

-- | toplevel parser for types
ty :: Parser Ty
ty = buildExpressionParser table factor <?> "type"
  where
    table  = [[Infix (reservedOp "->" >> return (:->)) AssocRight]]
    factor = prodOrSumTy term
    term   = parens ty <|> unitP <|> boolP


-- >>> testParser ty "Unit -> Unit"
-- Right (Prod [] :-> Prod [])

-- >>> testParser ty "Unit -> Unit + Unit -> Unit * Unit"
-- Right (Prod [] :-> (Sum [Prod [],Prod []] :-> Prod [Prod [],Prod []]))

-- >>> testParser ty "(Unit -> Unit) + Unit -> Bool"
-- Right (Sum [Prod [] :-> Prod [],Prod []] :-> Sum [Prod [],Prod []])

-- >>> testParser ty "(1 -> Bool) -> 1 * 1"
-- Right ((Prod [] :-> Sum [Prod [],Prod []]) :-> Prod [Prod [],Prod []])

-----------------------------------------------------------------

-- * Patterns

var :: Parser Tm 
var = Var <$> identifier

inj :: Parser Tm -> Parser Tm
inj p = 
        (symbol "Inj" >> Inj <$> lexeme natural <*> p)
    <|> (reserved "True" >> return (Inj 1 (Pair []))) 
    <|> (reserved "False" >> return (Inj 0 (Pair [])))

-- >>> testParser (inj var) "Inj0 x"
-- Right (Inj 0 (Var "x"))

-- >>> testParser (inj var) "Inj 1 x"
-- Right (Inj 1 (Var "x"))

-- >>> testParser (inj var) "True"
-- Right (Inj 0 (Pair []))


tuple :: Parser Tm -> Parser Tm
tuple p = do xs <- P.sepBy p comma
             case xs of 
               [] -> return (Pair [])
               [x] -> return x
               (_:_) -> return (Pair xs)

-- >>> testParser (parens (tuple var)) "()"
-- Right Unit

-- >>> testParser (parens (tuple var)) "(x,y)"
-- Right (Pair [Var "x",Var "y"])

-- >>> testParser (parens (tuple var) <|> tuple var) "x,y"
-- Right (Pair [Var "x",Var "y"])


-- The difficulty with parsing patterns is that we need to parse
-- between products (comma separated sequences of terms), 
-- type annotations (terms followed by a colon then a type), 
-- and single terms. All of these *start* with a single term, the 
-- difference is what happens next.
multiple :: Parser Tm -> Parser Tm
multiple p = try one <|> return (Pair []) where
  one = p >>= \x -> 
            (Ann x <$> (colon >> ty))
            <|> (comma >> 
                  do xs <- P.sepBy p comma
                     case xs of 
                        [] -> return x
                        _  -> return $ Pair (x:xs))
            <|> return x

-- >>> testParser (parens (multiple var)) "(x : 1)"
-- Right (Ann (Var "x") (Prod []))

-- >>> testParser (parens (multiple var)) "(x)"
-- Right (Var "x")

-- >>> testParser (parens (multiple var)) "(x,y,z)"
-- Right (Pair [Var "x",Var "y",Var "z"])

-- | A pattern produces an element of the term datatype 
-- but in a restricted set
pat :: Parser Tm 
pat = term <?> "pattern" where
   term = parens (multiple pat) 
        <|> inj pat 
        <|> var

-- >>> testParser pat "x"
-- Right (Var "x")


-- >>> testParser pat "()"
-- Right (Pair [])

-- >>> testParser pat "(x : 1)"
-- Right (Ann (Var "x") (Prod []))

-- >>> testParser pat "Inj1 ((x,Inj 0 y),())"
-- Right (Inj 1 (Pair [Pair [Var "x",Inj 0 (Var "y")],Pair []]))


-----------------------------------------------------------------
--- * Terms 

lambda :: Parser Tm 
lambda = do 
  reservedOp "\\" <|> reservedOp "λ"
  binds <- many1 identifier
  dot
  body <- tm
  return $ foldr Lam body binds

casetm :: Parser Tm
casetm = do
  reserved "case"
  cond <- tm
  reserved "of"
  optional (reservedOp "|")
  brs <- P.sepBy branch (reservedOp "|")
  return (Case cond brs)

branch :: Parser (Tm,Tm)
branch = do 
  p <- pat
  reservedOp "->"
  t <- tm
  return (p,t)

tm :: Parser Tm
tm = funapp <?> "expression" where

  funapp = do 
    f <- factor
    foldl App f <$> many factor

  factor = parens (multiple tm)
      <|> inj tm
      <|> iftm
      <|> casetm
      <|> lambda
      <|> lettm
      <|> iftm
      <|> var

-- >>> testParser tm "(x y) z"
-- Right (App (App (Var "x") (Var "y")) (Var "z"))

-- >>> testParser tm "() z"
-- Right (App (Pair []) (Var "z"))

-- >>> testParser tm "\\ x . \\ y . (x y) (x x)"
-- Right (Lam "x" (Lam "y" (App (App (Var "x") (Var "y")) (App (Var "x") (Var "x")))))

lettm :: Parser Tm
lettm =
  do
    reserved "let"
    x <- identifier
    reservedOp "="
    rhs <- tm
    reserved "in"
    body <- tm
    return $ App (Lam x body) rhs 

iftm :: Parser Tm
iftm = do 
  reserved "if" 
  cond <- tm 
  reserved "then"
  t1 <- tm
  reserved "else"
  t2 <- tm
  return (Case cond [(Inj 0 (Pair[]), t1), (Inj 1 (Pair []), t2)])

