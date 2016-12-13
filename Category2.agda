module Category2 where

open import Agda.Primitive
open import BaseLogic


{-
data Arrow {i j} (Obj : Set i) (Hom : Obj → Obj → Set j) : Set (i ⊔ j) where
 cons : (domain : Obj) → (range : Obj) → (val : Hom domain range) → Arrow Obj Hom 
-}
{-
record Arrow {i j} (Obj : Set i) (Hom : Obj → Obj → Set j) (o1 o2 : Obj) : Set (i ⊔ j) where
 field
  dom : Obj
  range : Obj
  val : Set j
  val = Hom dom range
-}

{-
record Arrow {i j} (Obj : Set i) (Hom : Obj → Obj → Set j) (o1 o2 : Obj) (v : Hom o1 o2) : Set (i ⊔ j) where
 field
  dom : Obj
  dom = o1
  
  range : Obj
  range = o2
 
  val : Hom dom range
  val = v
-}


{-
record Category₀ {i j} : Set (lsuc (i ⊔ j))  where
 field
  obj : Set i
  arrT : obj → obj → Set j
  hom : 
  id : (x : obj) → hom x x
  comp : (x y z : obj) → hom y z → hom x y → hom x z
-}
