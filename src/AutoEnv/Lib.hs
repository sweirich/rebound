-- imports and reexports libraries for Nat / Fin / Vec
{-# LANGUAGE ExplicitNamespaces #-}
module AutoEnv.Lib
  ( 
    module Data.SNat,
    type Type,
    module Data.Type.Equality,
    Nat(Z,S), SNat(SZ,SS), 
    Fin(FZ,FS), Vec(VNil, (:::)),
    ToInt(..),
    module Data.LocalName,
  )
where

import Data.Kind (Type)
import Data.Type.Equality
import Data.SNat
import Data.Vec (Vec(..))
import Data.Fin (Fin(FZ,FS))
import Data.LocalName
