{-# LANGUAGE
 FunctionalDependencies,
 UndecidableInstances, 
 ScopedTypeVariables,
 MultiParamTypeClasses,
 TypeSynonymInstances
 #-}
module KTypeStructures where

import qualified Data.Set as S
import Data.Monoid (mempty, mappend, mconcat)
import qualified Data.Map as M

import SCC

type Id = String

-----------
-- Kinds --
-----------
infixr 1 :~~>
infixr 1 :~~>>

{-*-}
data Kind = Kind :~~>> Kind
          | KindStar
          deriving (Eq, Ord, Show, Read)
                   
data KindOrder = KBot
               | KTop
               | KindOrder :~~> KindOrder
               | KOrder KOrder
               deriving (Eq, Ord, Show, Read)

data KOrder = KE
            | KL | KG
            | KS
            deriving (Eq, Ord, Show, Read, Enum)
                    
-------------------------------
-- Initial data/class syntax --
-- formally specified        --
-------------------------------

data UIType = UIApp UIType UIType 
            | UIVar Id 
            | UIConst UIConst
            deriving (Show, Eq, Ord, Read)
                     
data UIConst = UINamed Id
             | UIAnonymous UnionSum (M.Map Id UIType)
             | UIArrow
             deriving (Show, Eq, Ord, Read)

data UnionSum = Union
              | Sum
              deriving (Show, Eq, Ord, Read)
                       
data NamedType = 
  NamedType { namedTypeOp :: UnionSum 
            , namedTypeParameters :: [Id]
            , namedTypeMembers :: M.Map Id UIType     -- ^ constructors/records 
            , namedTypeInheritance :: M.Map Id [UIType] -- ^ the inheritence list.
            }
  deriving (Show, Eq, Ord, Read)


getTypeInheritences nmt = map (uncurry toInherit) $ M.toList $ namedTypeInheritance nmt
  where toInherit = foldl UIApp . UIConst . UINamed

-----------
-- Types --
-----------
data Type = TVar TyVar | TCon TyCon | TAp Type Type | TGen Int
          deriving (Eq, Ord, Show, Read)
data TyVar = TyVar Id KindOrder
           | TyRange Type Type
           deriving (Eq, Ord, Show, Read)
data TyCon = TyNamed Id (S.Set Id {- constructors/records -}) KindOrder
           | TyAnonymous UnionSum (M.Map Id Type) -- Anonymous constructor/object
           | TyArrow
           deriving (Eq, Ord, Show, Read)

---------------
-- Functions --
---------------

class HasKindOrder a where  
  kindOrderOf :: a -> KindOrder
  
class HasKOrder a where  
  kOrderOf :: a -> KOrder

-- Can't use KindOrder to directly check kinds.  Will need to use Kind.
instance HasKindOrder TyCon where
  kindOrderOf TyArrow = KOrder KG :~~> KOrder KL :~~> KOrder KE
  kindOrderOf (TyAnonymous us _) = kindOrderOf us
  kindOrderOf (TyNamed _ _ ko) = ko
  
instance HasKOrder UnionSum where  
  kOrderOf Union = KG
  kOrderOf Sum = KL
instance HasKindOrder UnionSum where  
  kindOrderOf = KOrder . kOrderOf
instance HasKindOrder Type where
  kindOrderOf (TVar v) = kindOrderOf v
  kindOrderOf (TCon c) = kindOrderOf c
  kindOrderOf (TGen _) = error "kind order of a type variable is not yet known"
  kindOrderOf (TAp t1 _) = case kindOrderOf t1 of
      _ :~~> k -> k
      _ -> error $ show t1 ++ " takes no parameters"
instance HasKindOrder TyVar where
  kindOrderOf (TyVar _ k) = k
  kindOrderOf (TyRange t1 _) = kindOrderOf t1


-- | @'getArgumentOrder' tfun@ returns what order we should flip the first
-- argument of tfun.   
getArgumentOrder :: HasKindOrder a => a -> KOrder
getArgumentOrder = getArg . kindOrderOf
  where getArg (k :~~> _) = getEnd k
        getArg v = getEnd v
        
        getEnd (_ :~~> k) = getEnd k
        getEnd KBot = KE
        getEnd KTop = KL
        getEnd (KOrder k) = k

kindOf :: HasKindOrder a => a -> Kind
kindOf = kindOf' . kindOrderOf
  where kindOf' (a :~~> b) = kindOf' a :~~>> kindOf' b
        kindOf' _ = KindStar



instance HasRefs NamedType Id where   
  getRefs n = mappend member_refs in_refs
    where member_refs = mconcat $ map getRefs $ M.elems $ namedTypeMembers n
          in_refs = mconcat $ map (mconcat . fmap getRefs) $ M.elems $ namedTypeInheritance n
instance HasRefs UIType Id where
  getRefs (UIApp a b) = mappend (getRefs a) (getRefs b)
  getRefs (UIVar _) = mempty
  getRefs (UIConst c) = getRefs c
instance HasRefs UIConst Id where
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
