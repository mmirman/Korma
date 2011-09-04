module KKindOrderInference where

import SCC
import KTypeStructures
import Data.Map (Map, (!))
import qualified Data.Map as M
import Control.Monad.RWS.Lazy
import Control.Monad.State
import Data.Functor ((<$>))
-----------------------------------------------
-- by this stage, we should know that the NamedTypes are properly kinded.
kindOrderInference :: Map Id NamedType -> Map Id KindOrder
kindOrderInference mp = totalKindOrderInferer $ map (\s->(s,mp!s)) <$> sortByRefs mp
                     -- no lambdas or let bound polymorphism, so scc sort is primitive

data KOConstraint = KOC KindOrder KindOrder

type KOInfer = State (Map Id KindOrder)
type KOBind = RWS (Map Id KindOrder) [KOConstraint] Int

totalKindOrderInferer l = execState (mapM bindingGroupKindOrderInferer l) (mempty)

bindingGroupKindOrderInferer :: [(Id,NamedType)] -> KOInfer ()
bindingGroupKindOrderInferer l = do
  mp <- get
  let (ko, _, constraints) = runRWS (mapM kindOrderInfererTop l) mp 0
  put mp


kindOrderInfererTop :: (Id,NamedType) -> KOBind KindOrder 
kindOrderInfererTop (s,k) = do
  undefined


kOglb a b = case (min a b, max a b) of
  (KE, _) -> KE
  (KL, KG) -> KE
  (a, _) -> a
