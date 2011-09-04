module KTypeBuilder where

import KTypeStructures
import KKindInference
import KKindOrderInference

import Data.Set hiding (map)
import Data.Map hiding ((!), map)

type ByName = Map Id TyCon
type ByConstructors = Map (Set Id) TyCon

-- in typeFinisher, we take each data/union in the map of NamedTypes, and 
-- figure out each's kind and kind-order.
typeFinisher :: (Map Id NamedType) -> (ByName, ByConstructors)
typeFinisher = undefined