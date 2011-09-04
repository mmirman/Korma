{-# LANGUAGE
 FunctionalDependencies,
 UndecidableInstances, 
 ScopedTypeVariables
 #-}
module SCC (sortByRefs, HasRefs(..)) where

import qualified Data.Set as S
import Data.Graph.Wrapper
import qualified Data.Map as M
import Data.Functor ((<$>))

class Ord r => HasRefs m r | m -> r where
  getRefs :: m -> S.Set r
  
sortByRefs:: HasRefs m r => M.Map r m -> [[r]]
sortByRefs = reverse . sccToLists . stronglyConnectedComponents . toGraph 

toGraph :: forall m r . HasRefs m r => M.Map r m -> Graph r r
toGraph refMap = fromListSimple mp  
  where mp :: [(r,[r])]
        mp = M.toList $ (S.toList . getRefs) <$> refMap
        
sccToLists :: [SCC r] -> [[r]]
sccToLists = map $ \scc -> case scc of
  AcyclicSCC i -> [i] 
  CyclicSCC l -> l
  
{- Hi, I'm a comment -}  