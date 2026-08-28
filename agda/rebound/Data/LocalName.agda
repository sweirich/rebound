{-# OPTIONS --erasure #-}

-- |
-- Module      : Data.LocalName
-- Description : User-supplied names, carried along for printing
--
-- A `LocalName` binds exactly one variable and records the name the
-- user wrote.  It has no effect on scoping or substitution -- it is
-- metadata that rides along at the binder so that output can be
-- readable.
module Data.LocalName where

open import Rebound.Lib
open import Rebound.Classes

record LocalName : Set where
  constructor mkLocalName
  field name : String
open LocalName public

instance
  SizedLocalName : Sized LocalName
  Sized.theSize SizedLocalName = N1
  Sized.size    SizedLocalName = λ _ → s1
