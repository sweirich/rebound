-- imports and reexports libraries for Nat / Fin / Vec
module Lib
  ( module Nat,
    module Fin,
    type Type,
    module Data.Type.Equality,
    Vec (..),
  )
where

import Data.Kind (Type)
import Data.Type.Equality
import Fin
import Nat
import Vec
