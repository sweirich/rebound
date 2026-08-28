{-# OPTIONS --erasure #-}

-- |
-- Module      : Rebound.Lib
-- Description : Library for dependent types
--
-- Imports and re-exports the basic definitions used throughout rebound.
module Rebound.Lib where

open import Data.Prelude       public
open import Data.Type.Equality public
open import Data.Nat           public
open import Data.Singleton     public
open import Data.Fin           public using (Fin; FZ; FS; f0; f1; f2; f3;
                                             shiftN; shift1; toNat; absurd; eqFin)
open import Data.Vec           public using (Vec; VNil; _:::_)
