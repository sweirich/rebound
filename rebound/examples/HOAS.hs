
module HOAS where

{-
This module demonstrates how to layer a HOAS-based representation 
on top of a de Bruijn representation, to make it easier to generate well scoped 
lambda terms.

It is based on Conor McBride's "Classy Hack"
https://mazzo.li/epilogue/index.html%3Fp=773.html

-}

import LC qualified     
import Data.Fin
import Rebound.Bind.Single
import Rebound

-- Here are some HOAS lambda calculus terms

tru :: Tm Z
tru = Lam $ \x -> Lam $ \y -> Var x

fls :: Tm Z
fls = Lam $ \x -> Lam $ \y -> Var y

app :: Tm Z 
app = Lam $ \f -> Lam $ \x -> App (Var f) (Var x)

omega :: Tm Z
omega = App delta delta where
    delta = Lam $ \x -> App (Var x) (Var x)

-- We can convert them to a de Bruijn-indexed 
-- representation easily

-- >>> cvt tru
-- (λ. (λ. 1))

-- >>> cvt fls
-- (λ. (λ. 0))

-- >>> cvt app 
-- (λ. (λ. (1 0)))

-- >>> cvt omega 
-- ((λ. (0 0)) (λ. (0 0)))


-- These terms are elements of the following datatype
-- that uses a form of "weak higher-order abstract syntax"
-- for variable binding. A type class constraint in the variable
-- constructor constructs the appropriate de Bruijn index.
data Tm (a :: Nat) where
  Var :: (b ⊆ a) => Proxy b -> Tm a
  App :: Tm a -> Tm a -> Tm a
  Lam :: (Proxy (S a) -> Tm (S a)) -> Tm a

instance Cvt Tm LC.Exp where
  cvt :: Tm m -> LC.Exp m
  cvt (Var x)   = LC.Var (cvtVar x)
  cvt (App a b) = LC.App (cvt a) (cvt b)
  cvt (Lam f)   = LC.Lam (cvtBind f)

------------------------------------------------------------
-- The rest of this file is independent of the language that we are using
-- and can be called reusable "library" code
-- It depends on overlapping instances

-- Conversion type class
class Cvt t u | t -> u where
  cvt :: t m -> u m

class (b :: Nat) ⊆ (a :: Nat) where 
    inj :: Fin b -> Fin a
instance {-# OVERLAPPING #-} n ⊆ n where inj = id
instance {-# OVERLAPPING #-} (o ~ S n, m ⊆ n) => m ⊆ o where inj = FS . inj
    
newtype Proxy b = P (Fin b)

zeroVar :: Proxy (S b)
zeroVar = P FZ

cvtVar :: (b ⊆ a) => Proxy b -> Fin a
cvtVar (P x) = inj x
 
cvtBind :: (Subst v u, Cvt t u) => (Proxy (S a) -> t (S a)) -> Bind v u a
cvtBind f = bind (cvt (f zeroVar))
