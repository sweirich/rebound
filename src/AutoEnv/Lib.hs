-- imports and reexports libraries for Nat / Fin / Vec
module AutoEnv.Lib
  ( module Data.Nat,
    module Data.SNat,
    type Type,
    module Data.Type.Equality,
    SNat(..), Nat(..), Fin(..), Vec (..),
    module Data.LocalName,
    ToInt(..)
  )
where

import Data.Kind (Type)
import Data.Type.Equality
import Data.Nat
import Data.SNat
import Data.Vec ( Vec(..) )
import Data.FinAux( Fin(..))

import Data.LocalName
