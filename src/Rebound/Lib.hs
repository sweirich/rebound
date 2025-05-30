-- imports and reexports libraries for Nat / Fin / Vec
{-# LANGUAGE ExplicitNamespaces #-}
module Rebound.Lib
  ( 
    module Data.SNat,
    type Type,
    module Data.Type.Equality,
    Nat(Z,S), 
    Fin, Fin_(..), fin_, f0, fs,
    Vec, Vec_(..), vec_, (|>),
    ToInt(..),
    module Data.LocalName,
  )
where

import Data.Kind (Type)
import Data.Type.Equality
import Data.SNat
import Data.Vec (Vec, Vec_(..), vec_, (|>))
import Data.Fin (Fin, Fin_(..), fin_, f0, fs)
import Data.LocalName
