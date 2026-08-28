{-# OPTIONS --erasure #-}

-- |
-- Module      : Rebound
-- Description : Efficient, Expressive, and Well-Scoped Binding
--
-- This top level module re-exports the core of the library.  It should
-- be used in conjunction with one (or more) module in @Rebound.Bind@.
--
-- This is an Agda port of a fragment of
-- <https://github.com/sweirich/rebound>, covering just enough of the
-- library to run the Haskell Symposium 2026 talk examples.
module Rebound where

open import Rebound.Lib     public
open import Rebound.Classes public
open import Rebound.Env     public
