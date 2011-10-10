{-# LANGUAGE
 GADTs,
 StandaloneDeriving,
 ExistentialQuantification
 #-}

module Compiler where

data Litteral


data Exp a where
  EApp    :: Exp a -> Exp b -> Exp Litteral
  ELam    :: Exp b -> Exp a
  EVar    :: Int -> Exp a  
  ECons   :: Int -> Exp a
  EChoose :: [(Int, Exp b)] -> Exp a
  
data Heap
data Stack

type HeapT = [Elem Heap]
type StackT = [Elem Stack]
data Elem a where
  Closure   :: HeapT -> Exp b -> Elem a
  FChoose   :: HeapT -> [(Int,Exp b)] -> Elem Stack
  Reference :: HeapT -> Int -> Elem Stack
  FProd     :: [Elem Stack] -> Elem Heap  
  Value     :: Exp b -> Elem Heap
data CState where 
  CState :: HeapT -> Exp a -> StackT -> CState
  Done :: Exp a -> CState
  
evaluate :: CState -> CState
evaluate (Done a) = error $ "Finished: "++show a 
evaluate (CState hp e st) = case (e, st) of
  (EApp a b, _) ->  -- APP
    CState hp a (Closure hp b:st)
  
  (EVar x, _) | Closure hp' b <- hp!!x  ->  -- VAREXP
    -- possibly add guard if out of index error doesn't cause otherwise  
    CState hp' b (Reference hp x:st)
    
  (EVar x, _) | Value b <- hp!!x  ->  -- VAR
    -- possibly add guard if out of index error doesn't cause otherwise  
    CState hp b st
    
  ( a , []) -> Done a  -- HALT
  
  (EVar _, Reference hp' x:sr) -> -- VAL
    CState (replace (Value e) x hp') e sr
  
  (_, Reference hp' x:sr) -> -- MEMOIZE
    CState (replace (Closure hp e) x hp') e sr
  
  (ELam a, Closure hp' b:sr) -> -- LAM
    CState (Closure hp' b:hp) a sr
  
  (EChoose l, Closure hp' a:sr) ->
    CState hp' a $ FChoose hp l:sr
    
  (ECons i, FChoose hp' l:sr) | Just b <- lookup i l
                              , FProd args:_ <- hp ->
    CState hp' b (args++sr)

  (ECons i, p:sr) -> case hp of
    FProd args:l -> CState ((FProd $ p:args):hp) (ECons i) sr

    

replace a 0 (v:l) = a:l
replace _ i [] = error $ "index "++show i++" is out of bounds"
replace a i (v:l) = v:(replace a (i-1) l)

{- 

Small step semantics:

heap               control            stack   

APP:  where (H,b) is the closure of the of the heap upon b.
H                   a b                 S     
---------------------------------------------- 
H                    a              (H, b):S    

LAM:
H                    \.a            (H',b):S 
----------------------------------------------- 
(H',b):H                   a               S        

CHOOSE:
 H               LChoose l                 (H',a):S
------------------------------------------------------
 H'                 a                (H, LChoose l):S

CONS:
 H              LCons i         (H', LChoose [...,(i, b),...]):S
-----------------------------------------------------------------
 H'                 b                       S



VAR:
 H               x                        S
------------------------------------------------   where (H',b) = H[x]
 H'              b                    (V.H,x):S        

VAL/MEMOIZE: where a is not an application or a Variable that references the heap.
 H'                     a                     (V.H,x):S
------------------------------------------------------------  
 H[ x |-> (H',a)]       a                       S

-}

deriving instance Show (Exp a)
deriving instance Show (Elem a)
deriving instance Show Heap
deriving instance Show Stack