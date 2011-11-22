{-# LANGUAGE
 GADTs,
 StandaloneDeriving,
 ExistentialQuantification,
 ScopedTypeVariables
 #-}

module Compiler where

data Litteral
data Value
data Heap
data Stack

type HeapT = [Elem Heap]
type StackT = [Elem Stack]

data CState where 
  CState :: HeapT -> Exp a -> StackT -> CState
  Done :: Exp a -> CState

data Elem a where
  Closure   :: HeapT -> Exp b -> Elem a
  FChoose   :: HeapT -> [(Int, Exp a)] -> Elem Stack
  Reference :: HeapT -> Int -> Elem Stack
  Value     :: Exp a -> Elem Heap

data Exp a where
  EApp    :: Exp a -> Exp b -> Exp Litteral
  ELam    :: Exp a -> Exp a
  EVar    :: Int -> Exp a
  EVal    :: Show b => b -> Exp a
  ECons   :: Int {- ^ name -} -> StackT -> Exp a
  EChoose :: [(Int, Exp a)] -> Exp a

($$) = EApp

infixl 2 <$ 
(<$) = EApp
infixr 1 $>
($>) = EApp

fix fun = (ELam$ fxx $$ fxx) $$ fun
  where fxx = (ELam$ f $$ (x $$ x) )
        f = EVar 1
        x = EVar 0
        
eval :: Exp Litteral -> String
eval l = eval' (CState [] l [])
  where eval' (Done a) = show a
        eval' f = eval' $ evaluate f

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
    -- this is probably not the smartest way of doing this, but whatevs.
    -- in a real - non anonymous program, we'd know how many inputs an ADT has.
    -- and can thus write "static" code to handle it.
    CState hp' a $ FChoose hp l:sr
    
  (ECons i l, FChoose hp' l':sr) -> case lookup i l' of
    Just a -> CState hp' a $ reverseConcat  l sr    
    Nothing -> error "type error"
    
  (ECons i l, a:sr) ->
    CState hp (ECons i $ a:l) sr
  
reverseConcat [] l = l
reverseConcat (a:r) l = reverseConcat r $ a:l

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

{-
data Exp a where
  EApp    :: Exp a -> Exp b -> Exp Litteral
  ELam    :: Exp a -> Exp a
  EVar    :: Int -> Exp a
  EVal    :: Show b => b -> Exp a
  ECons   :: Int {- ^ name -} -> StackT -> Exp a
  EChoose :: [(Int, Exp a)] -> Exp a

-}
