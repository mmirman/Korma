module KKindOrderInference where

import Data.Map (Map, (!))
import qualified Data.Map as M
import Control.Monad.RWS.Lazy
import Control.Monad.State
import Data.Functor ((<$>))

import SCC
import KTypeStructures

-----------------------------------------------
-- by this stage, we should know that the NamedTypes are properly kinded.
kindOrderInference :: Map Id NamedType -> Map Id KindOrder
kindOrderInference mp = totalKindOrderInferer $ map (\s->(s,mp!s)) <$> sortByRefs mp
                        -- no lambdas or let bound polymorphism, so scc sort is primitive

data KOConstraint = KOC KindOrder KindOrder

type KOInfer = State (Map Id KindOrder)
type KOBind = RWS (Map Id KindOrder) [KOConstraint] Int

totalKindOrderInferer :: [[(Id, NamedType)]] -> Map Id KindOrder
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

data LatticeVar a = LatticeRange a a
                  | LatticeVar Int
                  deriving (Eq)
                           
class RangeLattice a where
  top :: a
  bot :: a
  glb :: a -> a -> (a, a -> a)
  lub :: a -> a -> (a, a -> a)
  topVariable :: a -> Maybe (LatticeVar a)
  reduce :: a -> a -> [(a,a)]
  replace :: LatticeVar a -> a -> a -> a
  vToE :: LatticeVar a -> a
  occurs :: Int -> a -> Bool
  
-- does not support non nominal recursive bindings.
rangeUnify :: RangeLattice a => [(a,a)] -> LatticeVar a -> a
rangeUnify ((a,b):l) = case (topVariable a, topVariable b) of
  (Nothing,Nothing) -> rangeUnify $ (reduce a b)++l
  (Just s , Just t) -> case (s,t) of
    _ -> undefined
    
  (Just s@(LatticeRange aL aU), _) -> 
    let (aU', sub) = glb aU b
        repl = replace s $ vToE $ LatticeRange aL aU'
    in  repl . sub . (rangeUnify $ fmap repl <$> l)
  
  (Just s@(LatticeVar i), _) -> case occurs i b of
    True -> error "Occurs check"
    False -> repl . (rangeUnify $ fmap repl <$> l)
      where repl = replace s $ vToE $ LatticeRange bot b
            
  (Just s@(LatticeRange aL aU), _) -> 
    let (aU', sub) = glb aU b
        repl = replace s $ vToE $ LatticeRange aL aU'
    in  repl . sub . (rangeUnify $ fmap repl <$> l)
  
  (Just s@(LatticeVar i), _) -> case occurs i b of
    True -> error "Occurs check"
    False -> repl . (rangeUnify $ fmap repl <$> l)
      where repl = replace s $ vToE $ LatticeRange bot b

  