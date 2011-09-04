module KKindInference where

import KTypeStructures
import Data.Map hiding ((!), map)

-----------------------------------------------
-- here, we know nothing about the NamedTypes.
kindInference :: Map Id NamedType -> Map Id Kind
kindInference = undefined

