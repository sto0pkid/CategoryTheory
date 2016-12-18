module FAlgebras where

open import Agda.Primitive
open import BaseLogic
open import Category
open import Functor

record F-algebra {i j} (C : Category {i} {j}) (F : Functor C C) : Set (i ⊔ j) where
 field
  carrier : Category.obj C
  alg : (Category.hom C) ((Functor.omap F) carrier) carrier


record F-algebra-hom {i j} {C : Category {i} {j}} {F : Functor C C} (Aα : F-algebra C F) (Bβ : F-algebra C F) : Set (i ⊔ j) where 
 field
  f-hom : (Category.hom C) (F-algebra.carrier Aα) (F-algebra.carrier Bβ)
  hom-comm : ((Category.comp C)  f-hom (F-algebra.alg Aα)) ≡ ((Category.comp C) (F-algebra.alg Bβ) ((Functor.fmap F) f-hom)) 


F-algebra-category₀ : ∀ {i j} → (C : Category {i} {j}) → (F : Functor C C) →  Category₀ {j ⊔ i} {j ⊔ i}
F-algebra-category₀ {i} {j} C F = 
 record {
  obj = F-algebra C F;
  hom = F-algebra-hom;
  id = id'; 
  comp = comp'
 }
 where
  id' : (Aα : F-algebra C F) → (F-algebra-hom Aα Aα)
  id' Aα = record {
        f-hom = A⟲; 
        hom-comm = A⟲∘α≡α∘F[A⟲]
       }
     where 
      _∘_ : {x y z : Category.obj C} → Category.hom C y z → Category.hom C x y → Category.hom C x z
      _∘_ {x} {y} {z} g f = Category.comp C g f

      A : Category.obj C
      A = F-algebra.carrier Aα

      A⟲ : Category.hom C A A
      A⟲ = Category.id C A
      
      FA : Category.obj C
      FA = (Functor.omap F) A 

      F[A⟲] : Category.hom C FA FA
      F[A⟲] = (Functor.fmap F) A⟲ 

      [FA]⟲ : Category.hom C FA FA
      [FA]⟲ = Category.id C FA

      [FA]⟲≡F[A⟲] : [FA]⟲ ≡ F[A⟲]
      [FA]⟲≡F[A⟲] = (≡-↑↓ ((Functor.preserves-id F) A))

      α : Category.hom C FA A
      α = F-algebra.alg Aα  

      α∘_≡α : (f : Category.hom C FA FA) → Set j
      α∘ f ≡α = (α ∘ f) ≡ α

      A⟲∘α≡α : (A⟲ ∘ α) ≡ α
      A⟲∘α≡α = ((Category.left-id C) α)
 
      α∘[FA]⟲≡α : (α ∘ [FA]⟲) ≡ α
      α∘[FA]⟲≡α = ((Category.right-id C) α)
 
      α∘F[A⟲]≡α : (α ∘ F[A⟲]) ≡ α
      α∘F[A⟲]≡α = [x≡y]→[Px→Py] 
                       α∘_≡α 
                       [FA]⟲
                       F[A⟲] 
                       [FA]⟲≡F[A⟲]
                       α∘[FA]⟲≡α
      α≡α∘F[A⟲] : α ≡ (α ∘ F[A⟲])
      α≡α∘F[A⟲] = ≡-↑↓ α∘F[A⟲]≡α

      eq-chain : EqChain (A⟲ ∘ α) (α ∘ F[A⟲])
      eq-chain = A⟲∘α≡α ∷ (end α≡α∘F[A⟲])

      A⟲∘α≡α∘F[A⟲] : (A⟲ ∘ α) ≡ (α ∘ F[A⟲])
      A⟲∘α≡α∘F[A⟲] = EqChainExtract eq-chain

  comp' : {Aα Bβ Cγ : F-algebra C F} → (g : F-algebra-hom Bβ Cγ) → (f : F-algebra-hom Aα Bβ) → F-algebra-hom Aα Cγ
  comp' {Aα} {Bβ} {Cγ} g' f' = 
         record {
           f-hom = g ∘ f;
           hom-comm = [g∘f]∘α₁≡α₃∘F[g∘f]
          }
          where
            A₁ : Category.obj C
            A₁ = F-algebra.carrier Aα

            FA₁ : Category.obj C
            FA₁ = (Functor.omap F) A₁

            α₁ : Category.hom C FA₁ A₁
            α₁ = F-algebra.alg Aα

            A₂ : Category.obj C
            A₂ = F-algebra.carrier Bβ

            FA₂ : Category.obj C
            FA₂ = (Functor.omap F) A₂

            α₂ : Category.hom C FA₂ A₂
            α₂ = F-algebra.alg Bβ

            A₃ : Category.obj C
            A₃ = F-algebra.carrier Cγ

            FA₃ : Category.obj C
            FA₃ = (Functor.omap F) A₃
         
            α₃ : Category.hom C FA₃ A₃
            α₃ = F-algebra.alg Cγ

            f : Category.hom C A₁ A₂
            f = F-algebra-hom.f-hom f'

            g : Category.hom C A₂ A₃
            g = F-algebra-hom.f-hom g'

            F[f] : Category.hom C FA₁ FA₂
            F[f] = (Functor.fmap F) f

            F[g] : Category.hom C FA₂ FA₃
            F[g] = (Functor.fmap F) g

            _∘_ : {x y z : Category.obj C} → (g : Category.hom C y z) → (f : Category.hom C x y) → Category.hom C x z
            g ∘ f = Category.comp C g f

           
            g∘ : {x : Category.obj C} → (f : Category.hom C x A₂) → Category.hom C x A₃
            g∘ f = g ∘ f

            ∘F[f] : {z : Category.obj C} → (g : Category.hom C FA₂ z) → Category.hom C FA₁ z
            ∘F[f] g = g ∘ F[f]

            α₃∘ : {x : Category.obj C} → (g : Category.hom C x FA₃) → Category.hom C x A₃
            α₃∘ g = α₃ ∘ g 
            
                     
            f∘α₁≡α₂∘F[f] : (f ∘ α₁) ≡ (α₂ ∘ F[f])
            f∘α₁≡α₂∘F[f] = F-algebra-hom.hom-comm f'

            g∘α₂≡α₃∘F[g] : (g ∘ α₂) ≡ (α₃ ∘ F[g])
            g∘α₂≡α₃∘F[g] = F-algebra-hom.hom-comm g'

            F[g∘f] : Category.hom C FA₁ FA₃
            F[g∘f] = (Functor.fmap F) (g ∘ f)

            F[g]∘F[f]≡F[g∘f] : (F[g] ∘ F[f]) ≡ F[g∘f]
            F[g]∘F[f]≡F[g∘f] = ≡-↑↓ ((Functor.preserves-comp F) f g)

            [g∘f]∘α₁≡g∘[f∘α₁] : ((g ∘ f) ∘ α₁) ≡ (g ∘ (f ∘ α₁))
            [g∘f]∘α₁≡g∘[f∘α₁] = Category.assoc C g f α₁

            g∘[f∘α₁]≡g∘[α₂∘F[f]] : (g ∘ (f ∘ α₁)) ≡ (g ∘ (α₂ ∘  F[f]))
            g∘[f∘α₁]≡g∘[α₂∘F[f]] = [x≡y]→[fx≡fy] g∘ (f ∘ α₁) (α₂ ∘ F[f]) f∘α₁≡α₂∘F[f]

            g∘[α₂∘F[f]]≡[g∘α₂]∘F[f] : (g ∘ (α₂ ∘ F[f])) ≡ ((g ∘ α₂) ∘ F[f])
            g∘[α₂∘F[f]]≡[g∘α₂]∘F[f] = ≡-↑↓ ((Category.assoc C) g α₂ F[f])

            [g∘α₂]∘F[f]≡[α₃∘F[g]]∘F[f] : ((g ∘ α₂) ∘ F[f]) ≡ ((α₃ ∘ F[g]) ∘ F[f])
            [g∘α₂]∘F[f]≡[α₃∘F[g]]∘F[f] = [x≡y]→[fx≡fy] ∘F[f] (g ∘ α₂) (α₃ ∘ F[g]) g∘α₂≡α₃∘F[g]

            [α₃∘F[g]]∘F[f]≡α₃∘[F[g]∘F[f]] : ((α₃ ∘ F[g]) ∘ F[f]) ≡ (α₃ ∘ (F[g] ∘ F[f]))
            [α₃∘F[g]]∘F[f]≡α₃∘[F[g]∘F[f]] = (Category.assoc C) α₃ F[g] F[f]

            α₃∘[F[g]∘F[f]]≡α₃∘[F[g∘f]] : (α₃ ∘ (F[g] ∘ F[f])) ≡ (α₃ ∘ F[g∘f])
            α₃∘[F[g]∘F[f]]≡α₃∘[F[g∘f]] = [x≡y]→[fx≡fy] α₃∘ (F[g] ∘ F[f]) F[g∘f] F[g]∘F[f]≡F[g∘f]

            eq-chain : EqChain ((g ∘ f) ∘ α₁) (α₃ ∘ F[g∘f])
            eq-chain = [g∘f]∘α₁≡g∘[f∘α₁] 
                    ∷ (g∘[f∘α₁]≡g∘[α₂∘F[f]]
                    ∷ (g∘[α₂∘F[f]]≡[g∘α₂]∘F[f]
                    ∷ ([g∘α₂]∘F[f]≡[α₃∘F[g]]∘F[f]
                    ∷ ([α₃∘F[g]]∘F[f]≡α₃∘[F[g]∘F[f]]
                    ∷ (end α₃∘[F[g]∘F[f]]≡α₃∘[F[g∘f]]
                       )))))

            [g∘f]∘α₁≡α₃∘F[g∘f] : ((g ∘ f) ∘ α₁) ≡ (α₃ ∘ F[g∘f])
            [g∘f]∘α₁≡α₃∘F[g∘f] = EqChainExtract eq-chain

{-
F-algebra-category : ∀ {i j} → (C : Category {i} {j}) → (F : Functor C C) →  Category {j ⊔ i} {j ⊔ i}
F-algebra-category {i} {j} C F = 
 record {
  obj = Category₀.obj (F-algebra-category₀ C F);
  hom = Category₀.hom (F-algebra-category₀ C F);
  id = Category₀.id (F-algebra-category₀ C F);
  comp = Category₀.comp (F-algebra-category₀ C F)

{-
 Unfortunately these properties won't hold in ITT because the F-algebra homomorphisms involve
 the commutativity proofs, which will not necessarily be provably equal, even though the functions
 themselves are. Or maybe they will? If they don't, how can we weaken the expected equality in
 order to make them hold?
-}
-- left-id
-- right-id
-- assoc

 }
-}
