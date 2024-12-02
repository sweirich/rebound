-- imports and reexports libraries for Nat / Fin / Vec
module AutoEnv.Lib
  ( module Data.Nat,
    module Data.Fin,
    type Type,
    module Data.Type.Equality,
    Vec (..),
  )
where

import Data.Kind (Type)
import Data.Type.Equality
import Data.Fin
import Data.Nat
import Data.Vec ( Vec(..) )
