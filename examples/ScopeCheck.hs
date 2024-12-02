-- |
-- Module      : ScopeCheck
-- Description : Scope checking the Untyped lambda calculus
-- Stability   : experimental
--
-- This module demonstrates a translation from unscoped to well-scoped terms

module ScopeCheck where

import AutoEnv
import Data.Maybe (fromJust)
import LC qualified
import AutoEnv.Lib

-- | Named representation for the untyped lambda calculus
-- The type parameter 'a' is the variable type
data Exp (a :: Type) where
  Var :: a -> Exp a
  Lam :: a -> Exp a -> Exp a
  App :: Exp a -> Exp a -> Exp a

-- | Convert a named expression to deBruijn indicies, checking to make
-- sure that the expression is well scoped
scopeCheck :: (Eq a) => Exp a -> Maybe (LC.Exp Z)
scopeCheck = to []
  where
    to :: (Eq a) => [(a, Fin n)] -> Exp a -> Maybe (LC.Exp n)
    to vs (Var v) = do
      x <- lookup v vs
      return $ LC.Var x
    to vs (Lam v b) = do
      b' <- to ((v, FZ) : map (fmap FS) vs) b
      return $ LC.Lam (bind b')
    to vs (App f a) = do
      f' <- to vs f
      a' <- to vs a
      return $ LC.App f' a'


----------------------------------------------
-- Examples
----------------------------------------------

-- | Identity function
idExp :: Exp String
idExp = Lam "x" (Var "x")

-- | "True"
trueExp :: Exp String
trueExp = Lam "x" (Lam "y" (Var "x"))

-- >>> toScoped idExp
-- Variable not in scope: toScoped :: Exp String -> t_a1sSrU[sk:1]

-- >>> toScoped trueExp
-- Variable not in scope: toScoped :: Exp String -> t_a1sSrV[sk:1]

-- >>> toScoped (Lam "x" (Var "y"))
-- Variable not in scope: toScoped :: Exp String -> t_a1sSs9[sk:1]
