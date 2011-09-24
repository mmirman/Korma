{-# LANGUAGE
 TupleSections,
 ViewPatterns,
 FlexibleContexts,
 FlexibleInstances
 #-}

module KKindOrderInference where

import Data.Map (Map, (!))
import qualified Data.Map as M
import Control.Monad.RWS.Lazy
import Data.Functor ((<$>))

import SCC
import KTypeStructures
import RangeUnification

-----------------------------------------------
-- by this stage, we should know that the NamedTypes are properly kinded.
kindOrderInference :: Map Id NamedType -> Map Id KindOrder
kindOrderInference mp = totalKindOrderInferer $ map (\s->(s,mp!s)) <$> sortByRefs mp
                        -- no lambdas or let bound polymorphism, so scc sort is primitive

type KindOrders = Map Id KindOrder
type KindIneq = RangeInequality KindOrder
type KindIneqs = [KindIneq]
type KOBind = RWS KindOrders KindIneqs Int

totalKindOrderInferer :: [[(Id, NamedType)]] -> KindOrders
totalKindOrderInferer = foldr bindingGroupKindOrderInferer mempty

bindingGroupKindOrderInferer :: [(Id,NamedType)] -> KindOrders -> KindOrders
bindingGroupKindOrderInferer l mp = mappend mp_new mp
  where mp_new = (repVars $ refineUnifiedMap $ rangeUnify constraints) <$> all_binds
        -- here we begin the read with "mp" so as to remember the previously infered kindOrders
        (all_binds, _ {- num vars -}, constraints) = runRWS koit mp 0
        
        buildArrow (ko, binds) param = do
          ko' <- getLVar
          return (ko' :~~>> ko, M.insert param ko' binds)
        
        koit :: KOBind KindOrders -- should this really be a KOBind?
        koit = do
          lst <- forM l $ \(nm, nt) -> 
            -- bind the names to new variables/kinds before hand.
            foldM buildArrow (kindOrderOf $ namedTypeOp nt, mempty) 
              $ reverse $ namedTypeParameters $ nt
          
          -- now alter the environment with this.
          let allBinds :: KindOrders
              allBinds = foldr (mappend . snd) mempty lst
              
          local (mappend allBinds) $ forM (zip l lst) $ \((_,nt),(ko,_)) ->
            let params = reverse $ namedTypeParameters nt
                both [p] k = M.insert p k
                both (p:pars) (k :~~>> k') = M.insert p k . both pars k'
                both _ _ = error "does not take arguments"
            in -- Now we bind 'both' the parameters names to their corrosponding
               -- lattice variables in the kindOrderInference.  The binding only
               -- happens inside the kindOrderInfererTop, despite the variables
               -- living longer, as we would like to keep the parameters names
               -- from clashing.
               local (both params ko) $ kindOrderInfererTop nt
               
          return allBinds


-- | 'kindOrderInfererTop' recursively creates kind ordering-constraints.
kindOrderInfererTop k = mapM_ kindOrderGen member_types
  where member_types = mappend (getTypeInheritences k) (M.elems $ namedTypeMembers k)
        
class KindOrderGen a where 
  kindOrderGen :: a -> KOBind KindOrder
instance KindOrderGen UIType where
  kindOrderGen (UIVar i) = kindOrderGen i
  kindOrderGen (UIConst const) = kindOrderGen const
  kindOrderGen (UIApp t1 t2) = do
    k1 <- kindOrderGen t1 
    (ko, ki) <- case k1 of
      ki :~~>> ko ->
        return (ki, ko)
      _ -> do
        ki <- getLVar
        ko <- getLVar
        newConstraint (ki :~~>> ko) k1
        newConstraint k1 (ki :~~>> ko)
        return (ki, ko)
        
    k2 <- kindOrderGen t2        
    newConstraint k2 ki
    return ko
    
instance KindOrderGen UIConst where
  kindOrderGen (UINamed i) = kindOrderGen i
  kindOrderGen (UIArrow) = return $ KOrder KG :~~>> KOrder KL :~~>> KOrder KE
  kindOrderGen (UIAnonymous us tipes) = do
    mapM_ kindOrderGen $ M.elems tipes
    return $ kindOrderOf us
instance KindOrderGen [Char] where
  kindOrderGen i = do
    r <- ask 
    return $ r M.! i

  
newConstraint a b = do
  tell [RIneq a b]

repVars :: (LatticeVar KindOrder -> KindOrder) -> KindOrder -> KindOrder
repVars f (k :~~>> k') = (repVars f k) :~~>> (repVars f k')
repVars f (KVar k) = f k
repVars f t = t

---------------------------------------------------
-- Implementations of Lattice and RangeUnifiable --
---------------------------------------------------  

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
    