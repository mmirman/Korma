{-# LANGUAGE
 TupleSections
 #-}

module KKindOrderInference where

import Data.Map (Map, (!))
import qualified Data.Map as M
import Control.Monad.RWS.Lazy
import Control.Monad.State
import Data.Functor ((<$>))

import SCC
import KTypeStructures
import RangeUnification

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


instance Lattice KOrder where          
  top = KS
  bot = KE
  glb = getKOrderBound False
  lub = getKOrderBound True
    
getKOrderBound gb a b = (,id) $ case (min a b, max a b) of
    (KL, KG) -> if gb then top else bot
    (a, b) -> if gb then b else a

instance Lattice KindOrder where
  top = KTop
  bot = KBot
  glb = getKindOrderBound False
  lub = getKindOrderBound True

getKindOrderBound gb = getBound'
  where 
    same = getBound'
    diff = getKindOrderBound $ not gb
    errorMsg a b = error $ show a ++ " and "++ show b++" don't have a " ++ case gb of
        True -> "least upper bound"
        False -> "greatest lower bound"
    getBound' a b = case (min a b, max a b) of
      (ao@(KVar a), b) -> case (a,b) of
        (LatticeRange _ _, KVar b@(LatticeVar _)) -> (ao, substVar b a)
        (LatticeRange l _, KVar (LatticeRange l' _)) -> same l l'
        _ -> errorMsg a b
      (KTop, b) -> (if gb then top else b, id)
      (KBot, b) -> (if gb then b else bot, id)
    
      (a :~~>> a', b :~~>> b') -> (i_k :~~>> out_k, i_f . out_f )
        where (i_k , i_f) = diff a b
              (out_k, out_f) = same a' b'
      (_ :~~>> _, _) -> error "unexpected arrow"
    
      (KOrder a, KOrder b) -> (,id) $ KOrder $ fst $ case gb of 
        True -> lub a b
        False -> glb a b
      _ -> errorMsg a b
      
instance RangeUnifiable KindOrder where
  topVariable (KVar a) = Just a
  topVariable _ = Nothing
  
  reduce KBot _ = []
  reduce _ KTop = []
  reduce (a :~~>> a') (b :~~>> b') = [RIneq b a, RIneq a' b'] 
  reduce (KOrder a) (KOrder b) = case (a,b) of
    (KE, _) -> []
    (_, KS) -> []
    (a, b) | a == b -> []
    _ -> error "Kind Orders don't match."
  reduce a b = error $ show a ++ " and " ++ show b ++ " can not be unified"
    
  replaceVars s n = repVars
    where repVars (KVar v) | v == s = n
          repVars (a :~~>> b) = repVars a :~~>> repVars b 
          repVars other = other
  
  vToE = KVar
  
  occurs lv = occurs' 
    where occurs' (KVar l) | l == lv = True
          occurs' (KVar (LatticeRange a b)) = occurs' a || occurs' b
          occurs' (a :~~>> b) = occurs' a || occurs' b
          occurs' _ = False
    