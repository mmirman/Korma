module RangeUnification where

import Data.Functor ((<$>))

data LatticeVar a = LatticeRange a a
                  | LatticeVar Int
                  deriving (Eq)
                           
class RangeLattice a where
  top :: a
  bot :: a
  glb :: a -> a -> (a, LatticeVar a -> LatticeVar a)
  lub :: a -> a -> (a, LatticeVar a -> LatticeVar a)
  topVariable :: a -> Maybe (LatticeVar a)
  reduce :: a -> a -> [(a,a)]
  replaceVars :: LatticeVar a -> a -> a -> a
  vToE :: LatticeVar a -> a
  occurs :: Int -> a -> Bool

-- TODO: add error handling
-- does not support non nominal recursive bindings.
rangeUnify :: (Eq a, RangeLattice a) => [(a,a)] -> LatticeVar a -> a
rangeUnify [] = vToE
rangeUnify ((a,b):l) | a == b = rangeUnify l
rangeUnify ((a,b):l) = case (topVariable a, topVariable b) of
  (Nothing, Nothing) -> rangeUnify $ (reduce a b)++l
  (Just s, Just t) -> case (s,t) of
    (LatticeRange _ _, LatticeVar _) -> replv t s
    (LatticeVar _, _) -> replv s t    
    
    (LatticeRange sL sU, LatticeRange tL tU) -> case (sU == top, tL == bot) of 
      (True , True  ) -> rangeUnify $ (sL,tU):l      
      (True , False ) -> replr s (sL,tL)
      (False, True  ) -> replr t (sU,tU)
      (False, False ) -> rangeUnify (fmap (repS . repT) <$> l) . replS . replT . subS . subT
        where (tL', subT) = lub tL sU
              (sU', subS) = glb sU tL
              
              (replS, repS) = getRepl s $ LatticeRange sL sU'
              (replT, repT) = getRepl t $ LatticeRange tL' tU
              
  (Just s@(LatticeRange aL aU), _) ->  replr s (aL, aU') . sub
    where (aU', sub) = glb aU b
  (Just s@(LatticeVar i), _) -> case occurs i b of
    True  -> error "Occurs check"
    False -> replr s (bot,b)
            
  (_, Just t@(LatticeRange bL bU)) -> replr t (bL', bU) . sub
    where (bL', sub) = lub a bL
  
  (_, Just t@(LatticeVar i)) -> case occurs i a of
    True  -> error "Occurs check"
    False -> replr t (a,top)

  where replr f (a,b) = replv f $ LatticeRange a b
        replv f v = rangeUnify (fmap (replaceVars f $ vToE v) <$> l) . repl
          where repl s | s == f = v
                repl s | otherwise = s
                
        getRepl s s' = (\r -> if r==s then s' else r, replaceVars s $ vToE s')
