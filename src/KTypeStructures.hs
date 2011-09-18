{-# LANGUAGE
 FunctionalDependencies,
 UndecidableInstances, 
 ScopedTypeVariables,
 MultiParamTypeClasses,
 TypeSynonymInstances
 #-}
module KTypeStructures where

import Control.Monad.Trans.State.Lazy
import qualified Data.Set as S
import Data.Monoid
import Data.Functor ((<$>), fmap)
import qualified Data.Map as M
import Data.List (nub)

import RangeUnification
import SCC

type Id = String

-----------
-- Kinds --
-----------
infixr 1 :~~> 
infixl 1 :~~>> 

{-*-}

data Kind = Kind :~~> Kind
          | KStar
           deriving (Eq, Ord, Show, Read)

data KindOrder = KindOrder :~~>> KOrder
               | KNil
               | KVar Int
               deriving (Eq, Ord, Show, Read)

data KOrder = KE
            | KL | KG
            | KOVar Int
            deriving (Read, Show, Eq, Ord)

-------------------------------
-- Initial data/class syntax --
-- formally specified        --
-------------------------------

data UIType = UIApp UIType UIType 
            | UIVar Id 
            | UIConst UICon
            deriving (Show, Eq, Ord, Read)
                     
data UICon = UINamed Id
           | UIAnonymous UnionSum (M.Map Id UIType)
           | UIArrow
           deriving (Show, Eq, Ord, Read)

data UnionSum = Union
              | Sum 
              deriving (Show, Eq, Ord, Read)
                       
data NamedType = NamedType { namedTypeOp :: UnionSum 
                           , namedTypeParameters :: [Id]
                           , namedTypeMembers :: M.Map Id UIType  {- constructors/records -}
                           , namedTypeInheritance :: M.Map Id [UIType]
                           }
               deriving (Show, Eq, Ord, Read)
                        
-----------
-- Types --
-----------
data Type = TVar TyVar | TCon TyCon | TAp Type Type | TGen Int
          deriving (Eq, Ord, Show, Read)
data TyVar = TyVar Id Kind KindOrder
           | TyRange Type Type
           deriving (Eq, Ord, Show, Read)
data TyCon = TyNamed Id (S.Set Id) Kind KindOrder -- named constructor/object.
           | TyUnion (M.Map Id Type) -- Anonymous constructor/object
           | TySum (M.Map Id Type) -- Anonymous constructor/object             
           | TyArrow
           deriving (Eq, Ord, Show, Read)

---------------
-- Functions --
---------------
class HasKind a where
  kindOf :: a -> Kind
  
instance HasKind TyCon where 
  kindOf TyArrow = KStar :~~> KStar :~~> KStar
  kindOf (TyUnion _) = KStar
  kindOf (TySum _) = KStar
  kindOf (TyNamed _ _ k _) = k
instance HasKind Type where  
  kindOf (TVar v) = kindOf v
  kindOf (TCon c) = kindOf c
  kindOf (TAp t1 t2) = case (kindOf t1, kindOf t2) of
    ( a :~~> b , a' ) | a' == a -> b 
    ( _ :~~> _ , _) -> error $ show t1 ++" has a different kind argument than that of "++ show t2
    ( KStar , _ ) -> error $ show t1 ++ " takes no kind arguments"
instance HasKind TyVar where
  kindOf (TyVar _ k _) = k
  kindOf (TyRange t1 t2) | kindOf t1 == kindOf t2 = kindOf t1
  kindOf (TyRange t1 t2)  = error $ show t1 ++" has a different kind than that of "++ show t2


class HasKindOrder a where  
  kindOrderOf :: a -> KindOrder

-- When we encounter TAp t1 t2, find kindOrderOf t1 as , _ :~~>> ord, and use ord to control unification.
-- take the glb of the lhs and the rhs in this respect, and use those to control unification. 
instance HasKindOrder TyCon where 
  kindOrderOf TyArrow = KNil :~~>> KG :~~>> KL
  kindOrderOf (TyUnion _) = KNil
  kindOrderOf (TySum _) = KNil
  kindOrderOf (TyNamed _ _ _ ko) = ko
instance HasKindOrder Type where
  kindOrderOf (TVar v) = kindOrderOf v
  kindOrderOf (TCon c) = kindOrderOf c
  kindOrderOf (TAp t1 t2) = case kindOrderOf t1 of
    k :~~>> _  -> k
    KNil -> error $ show t1 ++ " takes no parameters"
instance HasKindOrder TyVar where
  kindOrderOf (TyVar _ _ k) = k
  kindOrderOf (TyRange t1 t2) = kindOrderOf t1

  

instance HasRefs NamedType Id where   
  getRefs n = mappend member_refs in_refs
    where member_refs = mconcat $ map getRefs $ M.elems $ namedTypeMembers n
          in_refs = mconcat $ map (mconcat . fmap getRefs) $ M.elems $ namedTypeInheritance n
instance HasRefs UIType Id where
  getRefs (UIApp a b) = mappend (getRefs a) (getRefs b)
  getRefs (UIVar _) = mempty
  getRefs (UIConst c) = getRefs c
instance HasRefs UICon Id where
  getRefs (UINamed i) = S.singleton i
  getRefs (UIAnonymous _ mp) = mconcat $ map getRefs $ M.elems mp
  getRefs UIArrow = mempty





-----------------------------------------------
-----------------------------------------------



{- question: how do we know that obj.k is from the object with member k?

 Answer:
 Named Objects's members are found by record name. 
 These record names should be Capitolized, along with Constructor names.
 
eg: 
class PersonData = Name String
                 & Year Int 
                 & Nationality { location Nation & citizen Bool }
                 & Sex [ Male | Female ]
 


union Nation = USA State
             | Ireland

- - - - - - - - - - - - - - - - - - - - - - - -
person = new Name = "hi"
             Year = 1990
             Nationality = new location = USA Nevada
                               citizen = True
             Sex = Male  

----------------------------------------------------------
or More involved:

class Geometry a = X a
                 & Y a


class Circle a = Direction [ In | Out ]
               & Radius a
               extends (Geometry Real)

class Polygon a = Sides Int
                extends (Geometry a)
- - - - - - - - - - - - - - - - - - - - - - - -
circle = new Direction = In
             X = 4.2
             Y = 12.0
             Radius = "cow"

circle = new Direction = In
             X = 4.2
             Y = 12.0
             Radius = "cow"


we infer that circle is of type Circle because it includes all of the requried 
constructors of circle, in the required types.  
ie, we associate Circle with the set of constructors (Direction, Radius, X, Y)
and infer, new{ Direction, X, Y, Radius} 
             :: forall a.  { Direction [ In | Out ] & Radius a &  X Real & Y Real } 
                -> Circle a


class Circle a = Moop (Circle a)

circ :: forall a . Circle a
circ = new Moop = circ

(not usefull)

but we would infer that here, new{ Moop } :: forall a . { Moop = a } -> Circle a 

Thus, we infer what new does based on the constructors it initializes.

If it initializes constructors that don't corrospond to any class, they should get
initialized as an anonymous class.

Each record name gets associated with a single class.  There can not be more than one
instance of the same record name in a program, similar to how there can not be
more than one instance of the same Constructor name in a program.

-}


  
  
{-  Kinding Rules.
****************************
Notes: 
(->) =:= (a.b. a -> b)

N a <: N' a'

and  N a = First (a -> Int)      such that N :: E :~~> G
         | Second (Int -> a) 

Suppose we are given N a <: N' a'.

We would need to break these down into N and N', so we use an odd process:
Find the first argument of klub (Kind(N), Kind(N')).  N should have Kind E:~~> * , so the first argument of the lub is E.

Thus, we check the result kind of the last argument of the kind, to get what we should do.

Thus, we break these down into N <: N' and a == a'.

Now, we check N <: N'.
   If N and N' are Union types  (G<:G): we check that every constructor of N is a constructor in N'.
   If N and N' are Sum types (L<:L): we check that every record of N' is a record in N.
   If N and N' are both arrows (E<:E): success.
   If N is a Sum and N' Union type (L<:G) : we fail. ( we can't know if the sum didn't contain more records at one point, or the union didn't contain more constructors)
   If N is a Union and N' Sum type (G<:L) : we check that N contains only one constructor, and N' contains only one record, and they are the same argument/record.

-------------------------------------

data Moap a m = Moap (m a -> a)

a :: L 
m :: (E -> G)

`--> Moap :: L -> (E -> G) -> G

-------------------------------------

data Moop a m = Moop (a -> m a)

a :: G
m :: (E -> L)

Moap :: G -> (E -> L) -> G

-------------------------------------
data Mp a m = Moop' (a -> Moop a m)
              Moap' (a -> Moap a m)


Now, the rules can be made a bit more lenient, because 
they should be allowed to change based on 
the actual subtyping rules in play: If we have 
Mp' a m <: Mp a m, where  data Mp' a = Moop' (a -> Moop a m).
we could re-infer Mp, with the rules of the smaller.
Thus, instead of using LUB to decide what to do, use the rules
of the smaller type. (This is undecidable I think, in the presence 
of type variables).



****************************

K|- k <<: k
K|- E <<: L <<: *
K|- E <<: G <<: *

  K|- k' <<: k     K|- l <<: l'
--------------------------------
  K|-  k :~~> l <<: k' :~~> l' 


  K|- t :: k    K|- k <<: l
-----------------------------
        K|- t :: l


     K, a :: k |- t :: l
-----------------------------
  K|-  (a . t) ::  k :~~> l


  K|- t :: k :~~> l     K|- t' :: k
-------------------------------------
          K|- t t' :: l

(a.b. a -> b)
K|- (->) :: G :~~> L :~~> E


  K|- t1 :: k1    ....     K|- tn :: kn
------------------------------------------
  K|- < C1: t1 || ... || Cn: tn > :: G


  K|- t1 :: k1    ....     K|- tn :: kn
------------------------------------------
  K|- { R1: t1 && ... && Rn: tn } :: L

-}
