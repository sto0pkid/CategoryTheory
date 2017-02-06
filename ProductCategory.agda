module ProductCategory where

open import Agda.Primitive
open import BaseLogic using (p≡[π₁-p,π₂-p] ; [x≡y]→[Px→Py])
open import Category
open import Data.Product
open import Data.PropositionalEquality
open import Data.EqChain

ProductCategory₀ : ∀ {i j k l} (C : Category {i} {j}) (D : Category {k} {l}) → Category₀ {i ⊔ k} {j ⊔ l}
ProductCategory₀ {i} {j} {k} {l} C D = 
 record {
  obj = (Category.obj C) × (Category.obj D);
  hom = λ p1 p2 → ((Category.hom C) (first p1) (first p2)) × ((Category.hom D) (second p1) (second p2));
  id = λ p → (((Category.id C) (first p)) , ((Category.id D) (second p)));
  comp = λ {x} {y} {z} g f → (((Category.comp C) (first g) (first f)) , ((Category.comp D) (second g) (second f))) 
 }


ProductCategory : ∀ {i j k l} (C : Category {i} {j}) (D : Category {k} {l}) → Category {i ⊔ k} {j ⊔ l}
ProductCategory {i} {j} {k} {l} C D = 
 record {
  obj = Category₀.obj P;
  hom = Category₀.hom P;
  id = Category₀.id P;
  comp = λ {x} {y} {z} → Category₀.comp P {x} {y} {z};
  left-id = λ {x} {y} → left-id' {x} {y};
  right-id = λ {x} {y} → right-id' {x} {y};
  assoc = λ {x} {y} {z} {w} → assoc' {x} {y} {z} {w}
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
    y⟲∘f≡y⟲∘[f₁,f₂] = [x≡y]→[Px→Py] y⟲∘f≡y⟲∘_ f (f₁ , f₂) f≡[f₁,f₂] refl

    y⟲∘[f₁,f₂]≡[y₁⟲∘f₁,y₂⟲∘f₂] : (y⟲ ∘ (f₁ , f₂)) ≡ ((y₁⟲ ∘₁ f₁) , (y₂⟲ ∘₂ f₂))
    y⟲∘[f₁,f₂]≡[y₁⟲∘f₁,y₂⟲∘f₂] = refl

    y₁⟲∘f₁≡f₁ : y₁⟲ ∘₁ f₁ ≡ f₁
    y₁⟲∘f₁≡f₁ = (Category.left-id C) f₁

    y₂⟲∘f₂≡f₂ : y₂⟲ ∘₂ f₂ ≡ f₂
    y₂⟲∘f₂≡f₂ = (Category.left-id D) f₂

    [_,y₂⟲∘f₂]≡[f₁,y₂⟲∘f₂] : (g : (Category.hom C) x₁ y₁) → Set (l ⊔ j)
    [ g ,y₂⟲∘f₂]≡[f₁,y₂⟲∘f₂] = (g , (y₂⟲ ∘₂ f₂)) ≡ (f₁ , (y₂⟲ ∘₂ f₂))

    [y₁⟲∘f₁,y₂⟲∘f₂]≡[f₁,y₂⟲∘f₂] : ((y₁⟲ ∘₁ f₁) , (y₂⟲ ∘₂ f₂)) ≡ (f₁ , (y₂⟲ ∘₂ f₂))
    [y₁⟲∘f₁,y₂⟲∘f₂]≡[f₁,y₂⟲∘f₂] = [x≡y]→[Px→Py] [_,y₂⟲∘f₂]≡[f₁,y₂⟲∘f₂] f₁ (y₁⟲ ∘₁ f₁) (≡-↑↓ y₁⟲∘f₁≡f₁) refl

    [f₁,_]≡[f₁,f₂] : (g : (Category.hom D) x₂ y₂) → Set (l ⊔ j)
    [f₁, g ]≡[f₁,f₂] = (f₁ , g) ≡ (f₁ , f₂)

    [f₁,y₂⟲∘f₂]≡[f₁,f₂] : (f₁ , (y₂⟲ ∘₂ f₂)) ≡ (f₁ , f₂)
    [f₁,y₂⟲∘f₂]≡[f₁,f₂] = [x≡y]→[Px→Py] [f₁,_]≡[f₁,f₂] f₂ (y₂⟲ ∘₂ f₂) (≡-↑↓ y₂⟲∘f₂≡f₂) refl

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
    f∘x⟲≡[f₁,f₂]∘x⟲ = [x≡y]→[Px→Py] f∘x⟲≡_∘x⟲ f (f₁ , f₂) f≡[f₁,f₂] refl

    [f₁,f₂]∘x⟲≡[f₁∘x₁⟲,f₂∘x₂⟲] : ((f₁ , f₂) ∘ x⟲) ≡ ((f₁ ∘₁ x₁⟲) , (f₂ ∘₂ x₂⟲))
    [f₁,f₂]∘x⟲≡[f₁∘x₁⟲,f₂∘x₂⟲] = refl

    f₁∘x₁⟲≡f₁ : (f₁ ∘₁ x₁⟲) ≡ f₁
    f₁∘x₁⟲≡f₁ = Category.right-id C f₁

    f₂∘x₂⟲≡f₂ : (f₂ ∘₂ x₂⟲) ≡ f₂
    f₂∘x₂⟲≡f₂ = Category.right-id D f₂

    [f₁∘x₁⟲,f₂∘x₂⟲]≡[_,f₂∘x₂⟲] : (g : Category.hom C x₁ y₁) → Set (l ⊔ j)
    [f₁∘x₁⟲,f₂∘x₂⟲]≡[ g ,f₂∘x₂⟲] = _≡_ {l ⊔ j} {(Category₀.hom P x y)} ((f₁ ∘₁ x₁⟲) , (f₂ ∘₂ x₂⟲)) (g , (f₂ ∘₂ x₂⟲))    

    [f₁∘x₁⟲,f₂∘x₂⟲]≡[f₁,f₂∘x₂⟲] : ((f₁ ∘₁ x₁⟲) , (f₂ ∘₂ x₂⟲)) ≡ (f₁ , (f₂ ∘₂ x₂⟲))
    [f₁∘x₁⟲,f₂∘x₂⟲]≡[f₁,f₂∘x₂⟲] = [x≡y]→[Px→Py] [f₁∘x₁⟲,f₂∘x₂⟲]≡[_,f₂∘x₂⟲] (f₁ ∘₁ x₁⟲) f₁ f₁∘x₁⟲≡f₁ refl

    [f₁,f₂∘x₂⟲]≡[f₁,_] : (g : Category.hom D x₂ y₂) → Set (l ⊔ j)
    [f₁,f₂∘x₂⟲]≡[f₁, g ] = _≡_ {l ⊔ j} {(Category₀.hom P x y)} (f₁ , (f₂ ∘₂ x₂⟲)) (f₁ , g)

    [f₁,f₂∘x₂⟲]≡[f₁,f₂] : (f₁ , (f₂ ∘₂ x₂⟲)) ≡ (f₁ , f₂)
    [f₁,f₂∘x₂⟲]≡[f₁,f₂] = [x≡y]→[Px→Py] [f₁,f₂∘x₂⟲]≡[f₁,_] (f₂ ∘₂ x₂⟲) f₂ f₂∘x₂⟲≡f₂ refl

    eq-chain : EqChain (f ∘ x⟲) f
    eq-chain = 
         f∘x⟲≡[f₁,f₂]∘x⟲
       ∷ [f₁,f₂]∘x⟲≡[f₁∘x₁⟲,f₂∘x₂⟲]
       ∷ [f₁∘x₁⟲,f₂∘x₂⟲]≡[f₁,f₂∘x₂⟲]
       ∷ [f₁,f₂∘x₂⟲]≡[f₁,f₂]
       ∷ (end [f₁,f₂]≡f)

    right-id-proof = EqChainExtract eq-chain






  assoc' : {x y z w : Category₀.obj P} → (h : Category₀.hom P z w) → (g : Category₀.hom P y z) → (f : Category₀.hom P x y) → 
           (compP {x} {y} {w} (compP {y} {z} {w} h g) f) ≡ (compP {x} {z} {w} h (compP {x} {y} {z} g f))
  assoc' {x} {y} {z} {w} h g f = assoc-proof
   where
    x₁ : Category.obj C
    x₁ = first x

    x₂ : Category.obj D
    x₂ = second x

    y₁ : Category.obj C
    y₁ = first y

    y₂ : Category.obj D
    y₂ = second y

    z₁ : Category.obj C
    z₁ = first z

    z₂ : Category.obj D
    z₂ = second z

    w₁ : Category.obj C
    w₁ = first w

    w₂ : Category.obj D
    w₂ = second w

    f₁ : Category.hom C x₁ y₁
    f₁ = first f
 
    f₂ : Category.hom D x₂ y₂
    f₂ = second f

    g₁ : Category.hom C y₁ z₁
    g₁ = first g

    g₂ : Category.hom D y₂ z₂
    g₂ = second g

    h₁ : Category.hom C z₁ w₁
    h₁ = first h

    h₂ : Category.hom D z₂ w₂
    h₂ = second h

    _∘₁_ = Category.comp C

    _∘₂_ = Category.comp D

    f≡[f₁,f₂] : f ≡ (f₁ , f₂)
    f≡[f₁,f₂] = p≡[π₁-p,π₂-p] f

    g≡[g₁,g₂] : g ≡ (g₁ , g₂)
    g≡[g₁,g₂] = p≡[π₁-p,π₂-p] g

    h≡[h₁,h₂] : h ≡ (h₁ , h₂)
    h≡[h₁,h₂] = p≡[π₁-p,π₂-p] h

    h∘g≡h∘_ : (g' : Category₀.hom P y z) → Set (l ⊔ j)
    h∘g≡h∘ g' = compP {y} {z} {w} h g ≡ compP {y} {z} {w} h g'

    h∘g≡h∘[g₁,g₂] : compP {y} {z} {w} h g ≡ compP {y} {z} {w} h (g₁ , g₂)
    h∘g≡h∘[g₁,g₂] = [x≡y]→[Px→Py] h∘g≡h∘_ g (g₁ , g₂) g≡[g₁,g₂] refl

    h∘[g₁,g₂]≡[h₁∘g₁,h₂∘g₂] : compP {y} {z} {w} h (g₁ , g₂) ≡ ((h₁ ∘₁ g₁) , (h₂ ∘₂ g₂))
    h∘[g₁,g₂]≡[h₁∘g₁,h₂∘g₂] = refl

    h∘g≡[h₁∘g₁,h₂∘g₂] : compP {y} {z} {w} h g ≡ ((h₁ ∘₁ g₁) , (h₂ ∘₂ g₂))
    h∘g≡[h₁∘g₁,h₂∘g₂] = ≡-⇶ h∘g≡h∘[g₁,g₂] h∘[g₁,g₂]≡[h₁∘g₁,h₂∘g₂]

    [h∘g]∘f≡_∘f : (q : Category₀.hom P y w) → Set (l ⊔ j)
    [h∘g]∘f≡ q ∘f = (compP {x} {y} {w} (compP {y} {z} {w} h g) f) ≡ (compP {x} {y} {w} q f)

    [h∘g]∘f≡[h₁∘g₁,h₂∘g₂]∘f : (compP {x} {y} {w} (compP {y} {z} {w} h g) f) ≡ (compP {x} {y} {w} ((h₁ ∘₁ g₁) , (h₂ ∘₂ g₂)) f)
    [h∘g]∘f≡[h₁∘g₁,h₂∘g₂]∘f = 
      [x≡y]→[Px→Py]
        [h∘g]∘f≡_∘f
        (compP {y} {z} {w} h g)
        ((h₁ ∘₁ g₁) , (h₂ ∘₂ g₂))
        h∘g≡[h₁∘g₁,h₂∘g₂]
        refl

    [h₁∘g₁,h₂∘g₂]∘f≡[[h₁∘g₁]∘f₁,[h₂∘g₂]∘f₂] : compP {x} {y} {w} ((h₁ ∘₁ g₁) , (h₂ ∘₂ g₂)) f ≡ (((h₁ ∘₁ g₁) ∘₁ f₁) , ((h₂ ∘₂ g₂) ∘₂ f₂))
    [h₁∘g₁,h₂∘g₂]∘f≡[[h₁∘g₁]∘f₁,[h₂∘g₂]∘f₂] = refl

    [h₁∘g₁]∘f₁≡h₁∘[g₁∘f₁] : ((h₁ ∘₁ g₁) ∘₁ f₁) ≡ (h₁ ∘₁ (g₁ ∘₁ f₁))
    [h₁∘g₁]∘f₁≡h₁∘[g₁∘f₁] = Category.assoc C h₁ g₁ f₁

    [h₂∘g₂]∘f₂≡h₂∘[g₂∘f₂] : ((h₂ ∘₂ g₂) ∘₂ f₂) ≡ (h₂ ∘₂ (g₂ ∘₂ f₂))
    [h₂∘g₂]∘f₂≡h₂∘[g₂∘f₂] = Category.assoc D h₂ g₂ f₂

    [[h₁∘g₁]∘f₁,[h₂∘g₂]∘f₂]≡[_,[h₂∘g₂]∘f₂] : (q  : Category.hom C x₁ w₁) → Set (l ⊔ j)
    [[h₁∘g₁]∘f₁,[h₂∘g₂]∘f₂]≡[ q ,[h₂∘g₂]∘f₂] = _≡_ {l ⊔ j} {Category₀.hom P x w} (((h₁ ∘₁ g₁) ∘₁ f₁) , ((h₂ ∘₂ g₂) ∘₂ f₂)) (q , ((h₂ ∘₂ g₂) ∘₂ f₂))

    [[h₁∘g₁]∘f₁,[h₂∘g₂]∘f₂]≡[h₁∘[g₁∘f₁],[h₂∘g₂]∘f₂] : (((h₁ ∘₁ g₁) ∘₁ f₁) , ((h₂ ∘₂ g₂) ∘₂ f₂)) ≡ ((h₁ ∘₁ (g₁ ∘₁ f₁)) , ((h₂ ∘₂ g₂) ∘₂ f₂))
    [[h₁∘g₁]∘f₁,[h₂∘g₂]∘f₂]≡[h₁∘[g₁∘f₁],[h₂∘g₂]∘f₂] = 
      [x≡y]→[Px→Py]
        [[h₁∘g₁]∘f₁,[h₂∘g₂]∘f₂]≡[_,[h₂∘g₂]∘f₂] 
        ((h₁ ∘₁ g₁) ∘₁ f₁)
        (h₁ ∘₁ (g₁ ∘₁ f₁))
        [h₁∘g₁]∘f₁≡h₁∘[g₁∘f₁]
        refl

    [h₁∘[g₁∘f₁],[h₂∘g₂]∘f₂]≡[h₁∘[g₁∘f₁],_] : (q : Category.hom D x₂ w₂) → Set (l ⊔ j)
    [h₁∘[g₁∘f₁],[h₂∘g₂]∘f₂]≡[h₁∘[g₁∘f₁], q ] = _≡_ {l ⊔ j} {Category₀.hom P x w} ((h₁ ∘₁ (g₁ ∘₁ f₁)) , ((h₂ ∘₂ g₂) ∘₂ f₂)) ((h₁ ∘₁ (g₁ ∘₁ f₁)) , q)

    [h₁∘[g₁∘f₁],[h₂∘g₂]∘f₂]≡[h₁∘[g₁∘f₁],h₂∘[g₂∘f₂]] : ((h₁ ∘₁ (g₁ ∘₁ f₁)) , ((h₂ ∘₂ g₂) ∘₂ f₂)) ≡ ((h₁ ∘₁ (g₁ ∘₁ f₁)) , (h₂ ∘₂ (g₂ ∘₂ f₂)))
    [h₁∘[g₁∘f₁],[h₂∘g₂]∘f₂]≡[h₁∘[g₁∘f₁],h₂∘[g₂∘f₂]] =
      [x≡y]→[Px→Py]
        [h₁∘[g₁∘f₁],[h₂∘g₂]∘f₂]≡[h₁∘[g₁∘f₁],_]
        ((h₂ ∘₂ g₂) ∘₂ f₂)
        (h₂ ∘₂ (g₂ ∘₂ f₂))
        [h₂∘g₂]∘f₂≡h₂∘[g₂∘f₂]
        refl

    g∘f≡g∘_ : (f' : Category₀.hom P x y) → Set (l ⊔ j)
    g∘f≡g∘ f' = compP {x} {y} {z} g f ≡ compP {x} {y} {z} g f'

    g∘f≡g∘[f₁,f₂] : compP {x} {y} {z} g f ≡ compP {x} {y} {z} g (f₁ , f₂)
    g∘f≡g∘[f₁,f₂] = [x≡y]→[Px→Py] g∘f≡g∘_ f (f₁ , f₂) f≡[f₁,f₂] refl

    g∘[f₁,f₂]≡[g₁∘f₁,g₂∘f₂] : compP {x} {y} {z} g (f₁ , f₂) ≡ ((g₁ ∘₁ f₁) , (g₂ ∘₂ f₂))
    g∘[f₁,f₂]≡[g₁∘f₁,g₂∘f₂] = refl

    g∘f≡[g₁∘f₁,g₂∘f₂] : compP {x} {y} {z} g f ≡ ((g₁ ∘₁ f₁) , (g₂ ∘₂ f₂))
    g∘f≡[g₁∘f₁,g₂∘f₂] = ≡-⇶ g∘f≡g∘[f₁,f₂] g∘[f₁,f₂]≡[g₁∘f₁,g₂∘f₂]

    h∘[g∘f]≡h∘_ : (v  : Category₀.hom P x z) → Set (l ⊔ j)
    h∘[g∘f]≡h∘ v = compP {x} {z} {w} h (compP {x} {y} {z} g f) ≡ compP {x} {z} {w} h v

    h∘[g∘f]≡h∘[g₁∘f₁,g₂∘f₂] : compP {x} {z} {w} h (compP {x} {y} {z} g f) ≡ compP {x} {z} {w} h ((g₁ ∘₁ f₁) , (g₂ ∘₂ f₂))
    h∘[g∘f]≡h∘[g₁∘f₁,g₂∘f₂] = [x≡y]→[Px→Py] h∘[g∘f]≡h∘_ (compP {x} {y} {z} g f) ((g₁ ∘₁ f₁) , (g₂ ∘₂ f₂)) g∘f≡[g₁∘f₁,g₂∘f₂] refl

    h∘[g₁∘f₁,g₂∘f₂]≡h∘[g∘f] : compP {x} {z} {w} h ((g₁ ∘₁ f₁) , (g₂ ∘₂ f₂)) ≡ compP {x} {z} {w} h (compP {x} {y} {z} g f)
    h∘[g₁∘f₁,g₂∘f₂]≡h∘[g∘f] = ≡-↑↓ h∘[g∘f]≡h∘[g₁∘f₁,g₂∘f₂]

    h∘[g₁∘f₁,g₂∘f₂]≡[h₁∘[g₁∘f₁],h₂∘[g₂∘f₂]] : compP {x} {z} {w} h ((g₁ ∘₁ f₁) , (g₂ ∘₂ f₂)) ≡ ((h₁ ∘₁ (g₁ ∘₁ f₁)) , (h₂ ∘₂ (g₂ ∘₂ f₂))) 
    h∘[g₁∘f₁,g₂∘f₂]≡[h₁∘[g₁∘f₁],h₂∘[g₂∘f₂]] = refl
 
    [h₁∘[g₁∘f₁],h₂∘[g₂∘f₂]]≡h∘[g₁∘f₁,g₂∘f₂] : ((h₁ ∘₁ (g₁ ∘₁ f₁)) , (h₂ ∘₂ (g₂ ∘₂ f₂))) ≡ (compP {x} {z} {w} h ((g₁ ∘₁ f₁) , (g₂ ∘₂ f₂)))
    [h₁∘[g₁∘f₁],h₂∘[g₂∘f₂]]≡h∘[g₁∘f₁,g₂∘f₂] = ≡-↑↓ h∘[g₁∘f₁,g₂∘f₂]≡[h₁∘[g₁∘f₁],h₂∘[g₂∘f₂]]


    eq-chain : EqChain (compP {x} {y} {w} (compP {y} {z} {w} h g) f) (compP {x} {z} {w} h (compP {x} {y} {z} g f))
    eq-chain = 
        [h∘g]∘f≡[h₁∘g₁,h₂∘g₂]∘f
      ∷ [h₁∘g₁,h₂∘g₂]∘f≡[[h₁∘g₁]∘f₁,[h₂∘g₂]∘f₂]
      ∷ [[h₁∘g₁]∘f₁,[h₂∘g₂]∘f₂]≡[h₁∘[g₁∘f₁],[h₂∘g₂]∘f₂]
      ∷ [h₁∘[g₁∘f₁],[h₂∘g₂]∘f₂]≡[h₁∘[g₁∘f₁],h₂∘[g₂∘f₂]]
      ∷ [h₁∘[g₁∘f₁],h₂∘[g₂∘f₂]]≡h∘[g₁∘f₁,g₂∘f₂]
      ∷ (end h∘[g₁∘f₁,g₂∘f₂]≡h∘[g∘f])

    assoc-proof = EqChainExtract eq-chain

