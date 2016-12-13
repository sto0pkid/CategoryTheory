module ProductCategory where

open import Agda.Primitive
open import BaseLogic
open import Category


ProductCategory₀ : ∀ {i j k l} (C : Category {i} {j}) (D : Category {k} {l}) → Category₀ {i ⊔ k} {j ⊔ l}
ProductCategory₀ {i} {j} {k} {l} C D = 
 record {
  obj = (Category.obj C) × (Category.obj D);
  hom = λ p1 p2 → ((Category.hom C) (outl p1) (outl p2)) × ((Category.hom D) (outr p1) (outr p2));
  id = λ p → (((Category.id C) (outl p)) , ((Category.id D) (outr p)));
  comp = λ g f → (((Category.comp C) (outl g) (outl f)) , ((Category.comp D) (outr g) (outr f))) 
 }

{-
  left-id : {x y : obj} → (f : hom x y) → (comp (id y) f) ≡ f
-}

{-
ProductCategory-left-id : ∀ {i j k l} (C : Category {i} {j}) (D : Category {k} {l}) → {x y : Category₀.obj (ProductCategory₀ C D)} → (f : Category₀.hom (ProductCategory₀ C D) x y) → (Category₀.comp (ProductCategory₀ C D) ((Category₀.id (ProductCategory₀ C D)) y) f) ≡ f
ProductCategory-left-id {i} {j} {k} {l} C D {x} {y} (f1 , f2) = proof
 where
  P : Category₀ {i ⊔ k} {j ⊔ l}
  P = ProductCategory₀ C D

  x1 : Category.obj C
  x1 = outl x

  x2 : Category.obj D
  x2 = outr x

  y1 : Category.obj C
  y1 = outl y

  y2 : Category.obj D
  y2 = outr y

  f : Category₀.hom P x y
  f = (f1 , f2)

  id-y : Category₀.hom P y y
  id-y = Category₀.id P y

  id-y∘f : Category₀.hom P x y
  id-y∘f = Category₀.comp P id-y f

  id-y1 : Category.hom C y1 y1
  id-y1 = Category.id C y1

  id-y2 : Category.hom D y2 y2
  id-y2 = Category.id D y2

  id-y1∘f1 : Category.hom C x1 y1
  id-y1∘f1 = Category.comp C id-y1 f1

  id-y2∘f2 : Category.hom D x2 y2
  id-y2∘f2 = Category.comp D id-y2 f2

  id-y≡[id-y1,id-y2] : id-y ≡ (id-y1 , id-y2)
  id-y≡[id-y1,id-y2] = refl (id-y1 , id-y2)

  

  [id-y1,id-y2]∘f≡[id-y1∘f1,id-y2∘f2] : Category₀.comp P (id-y1 , id-y2) f ≡ (id-y1∘f1 , id-y2∘f2)
  [id-y1,id-y2]∘f≡[id-y1∘f1,id-y2∘f2] = refl (id-y1∘f1 , id-y2∘f2)

  -∘f : (g : Category₀.hom P y y) → Set (l ⊔ j)
  -∘f g = Category₀.comp P g f ≡ (id-y1∘f1 , id-y2∘f2)

  id-y∘f≡[id-y1,id-y2]∘f : id-y∘f ≡ Category₀.comp P (id-y1 , id-y2) f
  id-y∘f≡[id-y1,id-y2]∘f = [x≡y]→[Px→Py] -∘f id-y (id-y1 , id-y2) id-y≡[id-y1,id-y2] (refl id-y∘f)

  id-y1∘f1≡f1 : id-y1∘f1 ≡ f1
  id-y1∘f1≡f1 = Category.left-id C f1

  id-y2∘f2≡f2 : id-y2∘f2 ≡ f2
  id-y2∘f2≡f2 = Category.left-id D f2
 
  [-,id-y2∘f2] : (g : Category.hom C x1 y1) → Set (l ⊔ j)
  [-,id-y2∘f2] g = (id-y1∘f1 , id-y2∘f2) ≡ (g , id-y2∘f2)

  [id-y1∘f1,id-y2∘f2]≡[f1,id-y2∘f2] : (id-y1∘f1 , id-y2∘f2) ≡ (f1 , id-y2∘f2)
  [id-y1∘f1,id-y2∘f2]≡[f1,id-y2∘f2] = [x≡y]→[Px→Py] [-,id-y2∘f2] id-y1∘f1 f1 id-y1∘f1≡f1 (refl (id-y1∘f1 , id-y2∘f2))

  [f1,-] : (g : Category.hom D x2 y2) → Set (l ⊔ j)
  [f1,-] g = (f1 , id-y2∘f2) ≡ (f1 , g)
 
  [f1,id-y2∘f2]≡[f1,f2] : (f1 , id-y2∘f2) ≡ (f1 , f2)
  [f1,id-y2∘f2]≡[f1,f2] = [x≡y]→[Px→Py] [f1,-] id-y2∘f2 f2 id-y2∘f2≡f2 (refl (f1 , id-y2∘f2))


  proof

-}

ProductCategory-right-id :  ∀ {i j k l} (C : Category {i} {j}) (D : Category {k} {l}) → {x y : Category₀.obj (ProductCategory₀ C D)} → (f : Category₀.hom (ProductCategory₀ C D) x y) → (Category₀.comp (ProductCategory₀ C D) f (Category₀.id (ProductCategory₀ C D) x)) ≡ f 
ProductCategory-right-id {i} {j} {k} {l} C D {x} {y} (f1 , f2) = proof
 where
  P : Category₀ {k ⊔ i} {l ⊔ j}
  P = ProductCategory₀ C D

  x1 : Category.obj C
  x1 = outl x

  x2 : Category.obj D
  x2 = outr x

  y1 : Category.obj C
  y1 = outl y

  y2 : Category.obj D
  y2 = outr y

  id-x : Category₀.hom P x x
  id-x = Category₀.id P x

  id-x1 : Category.hom C x1 x1
  id-x1 = Category.id C x1

  id-x2 : Category.hom D x2 x2
  id-x2 = Category.id D x2

  id-x≡[id-x1,id-x2] : id-x ≡ (id-x1 , id-x2)
  id-x≡[id-x1,id-x2] = refl (id-x1 , id-x2)

  f : Category₀.hom P x y
  f = (f1 , f2)

  f∘id-x : Category₀.hom P x y
  f∘id-x = Category₀.comp P f id-x

  f∘ : (g : Category₀.hom P x x) → Set (l ⊔ j)
  f∘ g = f∘id-x ≡ Category₀.comp P f g


  f∘id-x≡f∘[id-x1,id-x2] : f∘id-x ≡ Category₀.comp P f (id-x1 , id-x2)
  f∘id-x≡f∘[id-x1,id-x2] = [x≡y]→[Px→Py] f∘ id-x (id-x1 , id-x2) id-x≡[id-x1,id-x2] (refl f∘id-x)
  
  f1∘id-x1 : Category.hom C x1 y1
  f1∘id-x1 = Category.comp C f1 id-x1

  f2∘id-x2 : Category.hom D x2 y2
  f2∘id-x2 = Category.comp D f2 id-x2

  f∘[id-x1,id-x2]≡[f1∘id-x1,f2∘id-x2] : Category₀.comp P f (id-x1 , id-x2) ≡ (f1∘id-x1 , f2∘id-x2)
  f∘[id-x1,id-x2]≡[f1∘id-x1,f2∘id-x2] = refl (f1∘id-x1 , f2∘id-x2)

  f1∘id-x1≡f1 : f1∘id-x1 ≡ f1
  f1∘id-x1≡f1 = Category.right-id C f1

  f2∘id-x2≡f2 : f2∘id-x2 ≡ f2
  f2∘id-x2≡f2 = Category.right-id D f2

  [f1∘id-x1,f2∘id-x2]≡[-,f2∘id-x2] : (g : Category.hom C x1 y1) → Set (l ⊔ j)
  [f1∘id-x1,f2∘id-x2]≡[-,f2∘id-x2] g = (f1∘id-x1 , f2∘id-x2) ≡ (g , f2∘id-x2)

  [f1∘id-x1,f2∘id-x2]≡[f1,f2∘id-x2] : (f1∘id-x1 , f2∘id-x2) ≡ (f1 , f2∘id-x2)
  [f1∘id-x1,f2∘id-x2]≡[f1,f2∘id-x2] = [x≡y]→[Px→Py] [f1∘id-x1,f2∘id-x2]≡[-,f2∘id-x2] f1∘id-x1 f1 f1∘id-x1≡f1 (refl (f1∘id-x1 , f2∘id-x2))

  [f1,f2∘id-x2]≡[f1,-] : (g : Category.hom D x2 y2) → Set (l ⊔ j)
  [f1,f2∘id-x2]≡[f1,-] g = (f1 , f2∘id-x2) ≡ (f1 , g)

  [f1,f2∘id-x2]≡[f1,f2] : (f1 , f2∘id-x2) ≡ (f1 , f2)
  [f1,f2∘id-x2]≡[f1,f2] = [x≡y]→[Px→Py] [f1,f2∘id-x2]≡[f1,-] f2∘id-x2 f2 f2∘id-x2≡f2 (refl (f1 , f2∘id-x2))

  

{-
  f1∘id-x1≡f1 :
-}
  --proof : (Category₀.comp (ProductCategory₀ C D) f (Category₀.id (ProductCategory₀ C D) x)) ≡ f
  proof : (Category₀.comp (ProductCategory₀ C D) (f1 , f2) (Category₀.id (ProductCategory₀ C D) x)) ≡ (f1 , f2)
  proof = 
    ≡-⇶ f∘id-x≡f∘[id-x1,id-x2]
   (≡-⇶ f∘[id-x1,id-x2]≡[f1∘id-x1,f2∘id-x2]
   (≡-⇶ [f1∘id-x1,f2∘id-x2]≡[f1,f2∘id-x2]
         [f1,f2∘id-x2]≡[f1,f2]
   ))
  

{- 
  : id-y∘f ≡ (f1 , f2)
  proof = 
      ≡-⇶ id-y∘f≡[id-y1,id-y2]∘f 
     (≡-⇶ [id-y1,id-y2]∘f≡[id-y1∘f1,id-y2∘f2]
     (≡-⇶ [id-y1∘f1,id-y2∘f2]≡[f1,id-y2∘f2]
          [f1,id-y2∘f2]≡[f1,f2] 
      ))
-}
{-
ProductCategory : ∀ {i j k l} (C : Category {i} {j}) (D : Category {k} {l}) → Category {i ⊔ k} {j ⊔ l}
ProductCategory {i} {j} {k} {l} C D = 
 record {
  obj = Category₀.obj (ProductCategory₀ C D);
  hom = Category₀.hom (ProductCategory₀ C D);
  id = Category₀.id (ProductCategory₀ C D);
  comp = Category₀.comp (ProductCategory₀ C D);
{-
  left-id = λ f → refl ((outl f) , (outr f))
-}
 }
-}
