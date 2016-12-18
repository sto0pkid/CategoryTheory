module ProductCategory where

open import Agda.Primitive
open import BaseLogic
open import Category


ProductCategory₀ : ∀ {i j k l} (C : Category {i} {j}) (D : Category {k} {l}) → Category₀ {i ⊔ k} {j ⊔ l}
ProductCategory₀ {i} {j} {k} {l} C D = 
 record {
  obj = (Category.obj C) × (Category.obj D);
  hom = λ p1 p2 → ((Category.hom C) (first p1) (first p2)) × ((Category.hom D) (second p1) (second p2));
  id = λ p → (((Category.id C) (first p)) , ((Category.id D) (second p)));
  comp = λ g f → (((Category.comp C) (first g) (first f)) , ((Category.comp D) (second g) (second f))) 
 }


ProductCategory : ∀ {i j k l} (C : Category {i} {j}) (D : Category {k} {l}) → Category {i ⊔ k} {j ⊔ l}
ProductCategory {i} {j} {k} {l} C D = 
 record {
  obj = Category₀.obj P;
  hom = Category₀.hom P;
  id = Category₀.id P;
  comp = Category₀.comp P;
  left-id = left-id';
  right-id = right-id';
  assoc = assoc'
 }
 where
  P = ProductCategory₀ {i} {j} {k} {l} C D
  objP = Category₀.obj P
  homP = Category₀.hom P
  compP = Category₀.comp P
  idP = Category₀.id P



  left-id' : {x y : objP} → (f : homP x y) → (compP {x} {y} {y} (idP y) f) ≡ f
  left-id' {x} {y} f = left-id-proof
   where
    x₁ : Category.obj C
    x₁ = first x

    x₂ : Category.obj D
    x₂ = second x

    y₁ : Category.obj C
    y₁ = first y
  
    y₂ : Category.obj D
    y₂ = second y

    y⟲ : homP y y
    y⟲ = idP y

    y₁⟲ : (Category.hom C) y₁ y₁ 
    y₁⟲ =  (Category.id C) y₁

    y₂⟲ : (Category.hom D) y₂ y₂
    y₂⟲ = (Category.id D) y₂

    f₁ : (Category.hom C) x₁ y₁
    f₁ = first f

    f₂ : (Category.hom D) x₂ y₂
    f₂ = second f

    _∘_ = Category₀.comp P {x} {y} {y}

    _∘₁_ = Category.comp C

    _∘₂_ = Category.comp D
    
    f≡[f₁,f₂] : f ≡ (f₁ , f₂)
    f≡[f₁,f₂] = p≡[π₁-p,π₂-p] f

    [f₁,f₂]≡f : (f₁ , f₂) ≡ f
    [f₁,f₂]≡f = ≡-↑↓ f≡[f₁,f₂]

    y⟲∘f≡y⟲∘_ : (g : (Category₀.hom P) x y) → Set (l ⊔ j)
    y⟲∘f≡y⟲∘ g = (y⟲ ∘ f) ≡ (y⟲ ∘ g)

    y⟲∘f≡y⟲∘[f₁,f₂] : (y⟲ ∘ f) ≡ (y⟲ ∘ (f₁ , f₂))
    y⟲∘f≡y⟲∘[f₁,f₂] = [x≡y]→[Px→Py] y⟲∘f≡y⟲∘_ f (f₁ , f₂) f≡[f₁,f₂] (refl (y⟲ ∘ f))

    y⟲∘[f₁,f₂]≡[y₁⟲∘f₁,y₂⟲∘f₂] : (y⟲ ∘ (f₁ , f₂)) ≡ ((y₁⟲ ∘₁ f₁) , (y₂⟲ ∘₂ f₂))
    y⟲∘[f₁,f₂]≡[y₁⟲∘f₁,y₂⟲∘f₂] = refl ((y₁⟲ ∘₁ f₁) , (y₂⟲ ∘₂ f₂))

    y₁⟲∘f₁≡f₁ : y₁⟲ ∘₁ f₁ ≡ f₁
    y₁⟲∘f₁≡f₁ = (Category.left-id C) f₁

    y₂⟲∘f₂≡f₂ : y₂⟲ ∘₂ f₂ ≡ f₂
    y₂⟲∘f₂≡f₂ = (Category.left-id D) f₂

    [_,y₂⟲∘f₂]≡[f₁,y₂⟲∘f₂] : (g : (Category.hom C) x₁ y₁) → Set (l ⊔ j)
    [ g ,y₂⟲∘f₂]≡[f₁,y₂⟲∘f₂] = (g , (y₂⟲ ∘₂ f₂)) ≡ (f₁ , (y₂⟲ ∘₂ f₂))

    [y₁⟲∘f₁,y₂⟲∘f₂]≡[f₁,y₂⟲∘f₂] : ((y₁⟲ ∘₁ f₁) , (y₂⟲ ∘₂ f₂)) ≡ (f₁ , (y₂⟲ ∘₂ f₂))
    [y₁⟲∘f₁,y₂⟲∘f₂]≡[f₁,y₂⟲∘f₂] = [x≡y]→[Px→Py] [_,y₂⟲∘f₂]≡[f₁,y₂⟲∘f₂] f₁ (y₁⟲ ∘₁ f₁) (≡-↑↓ y₁⟲∘f₁≡f₁) (refl (f₁ , (y₂⟲ ∘₂ f₂)))

    [f₁,_]≡[f₁,f₂] : (g : (Category.hom D) x₂ y₂) → Set (l ⊔ j)
    [f₁, g ]≡[f₁,f₂] = (f₁ , g) ≡ (f₁ , f₂)

    [f₁,y₂⟲∘f₂]≡[f₁,f₂] : (f₁ , (y₂⟲ ∘₂ f₂)) ≡ (f₁ , f₂)
    [f₁,y₂⟲∘f₂]≡[f₁,f₂] = [x≡y]→[Px→Py] [f₁,_]≡[f₁,f₂] f₂ (y₂⟲ ∘₂ f₂) (≡-↑↓ y₂⟲∘f₂≡f₂) (refl (f₁ , f₂))

    eq-chain : EqChain (y⟲ ∘ f) f
    eq-chain = 
          y⟲∘f≡y⟲∘[f₁,f₂] 
        ∷ y⟲∘[f₁,f₂]≡[y₁⟲∘f₁,y₂⟲∘f₂] 
        ∷ [y₁⟲∘f₁,y₂⟲∘f₂]≡[f₁,y₂⟲∘f₂]
        ∷ [f₁,y₂⟲∘f₂]≡[f₁,f₂]
        ∷ (end [f₁,f₂]≡f)

    left-id-proof = EqChainExtract eq-chain

  right-id' : {x y : objP} → (f : homP x y) → (compP {x} {x} {y} f (idP x)) ≡ f
  right-id' {x} {y} f = right-id-proof
   where
    x₁ : Category.obj C
    x₁ = first x

    x₂ : Category.obj D
    x₂ = second x

    y₁ : Category.obj C
    y₁ = first y
  
    y₂ : Category.obj D
    y₂ = second y

    x⟲ : homP x x
    x⟲ = idP x

    x₁⟲ : (Category.hom C) x₁ x₁ 
    x₁⟲ =  (Category.id C) x₁

    x₂⟲ : (Category.hom D) x₂ x₂
    x₂⟲ = (Category.id D) x₂

    f₁ : (Category.hom C) x₁ y₁
    f₁ = first f

    f₂ : (Category.hom D) x₂ y₂
    f₂ = second f

    _∘_ = Category₀.comp P {x} {x} {y}

    _∘₁_ = Category.comp C {x₁} {x₁} {y₁}

    _∘₂_ = Category.comp D {x₂} {x₂} {y₂}
    
    f≡[f₁,f₂] : f ≡ (f₁ , f₂)
    f≡[f₁,f₂] = p≡[π₁-p,π₂-p] f

    [f₁,f₂]≡f : (f₁ , f₂) ≡ f
    [f₁,f₂]≡f = ≡-↑↓ f≡[f₁,f₂]

    f∘x⟲≡_∘x⟲ : (g : Category₀.hom P x y) → Set (l ⊔ j)
    f∘x⟲≡ g ∘x⟲ = (f ∘ x⟲) ≡ (g ∘ x⟲)

    f∘x⟲≡[f₁,f₂]∘x⟲ : (f ∘ x⟲) ≡ ((f₁ , f₂) ∘ x⟲)
    f∘x⟲≡[f₁,f₂]∘x⟲ = [x≡y]→[Px→Py] f∘x⟲≡_∘x⟲ f (f₁ , f₂) f≡[f₁,f₂] (refl (f ∘ x⟲))

    [f₁,f₂]∘x⟲≡[f₁∘x₁⟲,f₂∘x₂⟲] : ((f₁ , f₂) ∘ x⟲) ≡ ((f₁ ∘₁ x₁⟲) , (f₂ ∘₂ x₂⟲))
    [f₁,f₂]∘x⟲≡[f₁∘x₁⟲,f₂∘x₂⟲] = refl ((f₁ ∘₁ x₁⟲) , (f₂ ∘₂ x₂⟲))

    f₁∘x₁⟲≡f₁ : (f₁ ∘₁ x₁⟲) ≡ f₁
    f₁∘x₁⟲≡f₁ = Category.right-id C f₁

    f₂∘x₂⟲≡f₂ : (f₂ ∘₂ x₂⟲) ≡ f₂
    f₂∘x₂⟲≡f₂ = Category.right-id D f₂

    [f₁∘x₁⟲,f₂∘x₂⟲]≡[_,f₂∘x₂⟲] : (g : Category.hom C x₁ y₁) → Set (l ⊔ j)
    [f₁∘x₁⟲,f₂∘x₂⟲]≡[ g ,f₂∘x₂⟲] = _≡_ {l ⊔ j} {(Category₀.hom P x y)} ((f₁ ∘₁ x₁⟲) , (f₂ ∘₂ x₂⟲)) (g , (f₂ ∘₂ x₂⟲))    

    [f₁∘x₁⟲,f₂∘x₂⟲]≡[f₁,f₂∘x₂⟲] : ((f₁ ∘₁ x₁⟲) , (f₂ ∘₂ x₂⟲)) ≡ (f₁ , (f₂ ∘₂ x₂⟲))
    [f₁∘x₁⟲,f₂∘x₂⟲]≡[f₁,f₂∘x₂⟲] = [x≡y]→[Px→Py] [f₁∘x₁⟲,f₂∘x₂⟲]≡[_,f₂∘x₂⟲] (f₁ ∘₁ x₁⟲) f₁ f₁∘x₁⟲≡f₁ (refl ((f₁ ∘₁ x₁⟲) , (f₂ ∘₂ x₂⟲)))

    [f₁,f₂∘x₂⟲]≡[f₁,_] : (g : Category.hom D x₂ y₂) → Set (l ⊔ j)
    [f₁,f₂∘x₂⟲]≡[f₁, g ] = _≡_ {l ⊔ j} {(Category₀.hom P x y)} (f₁ , (f₂ ∘₂ x₂⟲)) (f₁ , g)

    [f₁,f₂∘x₂⟲]≡[f₁,f₂] : (f₁ , (f₂ ∘₂ x₂⟲)) ≡ (f₁ , f₂)
    [f₁,f₂∘x₂⟲]≡[f₁,f₂] = [x≡y]→[Px→Py] [f₁,f₂∘x₂⟲]≡[f₁,_] (f₂ ∘₂ x₂⟲) f₂ f₂∘x₂⟲≡f₂ (refl (f₁ , (f₂ ∘₂ x₂⟲)))

    eq-chain : EqChain (f ∘ x⟲) f
    eq-chain = 
         f∘x⟲≡[f₁,f₂]∘x⟲
       ∷ [f₁,f₂]∘x⟲≡[f₁∘x₁⟲,f₂∘x₂⟲]
       ∷ [f₁∘x₁⟲,f₂∘x₂⟲]≡[f₁,f₂∘x₂⟲]
       ∷ [f₁,f₂∘x₂⟲]≡[f₁,f₂]
       ∷ (end [f₁,f₂]≡f)

    right-id-proof = EqChainExtract eq-chain

  assoc' : {x y z w : Category₀.obj P} → (f : Category₀.hom P x y) → (g : Category₀.hom P y z) → (h : Category₀.hom P z w) → 
           (compP {x} {y} {w} (compP {y} {z} {w} h g) f) ≡ (compP {x} {z} {w} h (compP {x} {y} {z} g f))
  assoc' {x} {y} {z} {w} f g h = assoc-proof
   where
    
    assoc-proof


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

{-
ProductCategory-right-id :  ∀ {i j k l} (C : Category {i} {j}) (D : Category {k} {l}) → {x y : Category₀.obj (ProductCategory₀ C D)} → (f : Category₀.hom (ProductCategory₀ C D) x y) → (Category₀.comp (ProductCategory₀ C D) f (Category₀.id (ProductCategory₀ C D) x)) ≡ f 
ProductCategory-right-id {i} {j} {k} {l} C D {x} {y} (f1 , f2) = proof
 where
  P : Category₀ {k ⊔ i} {l ⊔ j}
  P = ProductCategory₀ C D

  x1 : Category.obj C
  x1 = first x

  x2 : Category.obj D
  x2 = second x

  y1 : Category.obj C
  y1 = first y

  y2 : Category.obj D
  y2 = second y

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
-}

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
