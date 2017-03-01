module Functions where

open import Agda.Primitive
open import Data.Product
open import Data.PropositionalEquality

{-
Functions are continuous with respect to propositional equality.
Functions behave functorially with respect to propositional equality.
-}
continuity : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → (x y : A) → x ≡ y → (f x) ≡ (f y)
continuity {i} {j} {A} {B} f x .x refl = refl


_∘_ : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → (B → C) → (A → B) → (A → C)
(g ∘ f) a = g (f a)

∘-assoc : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {D : Set l} → (h : C → D) → (g : B → C) → (f : A → B) → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
∘-assoc {i} {j} {k} {l} {A} {B} {C} {D} h g f = refl

surjective : ∀ {i j} {A : Set i} {B : Set j} → (A → B) → Set (i ⊔ j)
surjective {i} {j} {A} {B} f = (b : B) → ∃ a ∈ A , ((f a) ≡ b)

injective : ∀ {i j} {A : Set i} {B : Set j} → (A → B) → Set (i ⊔ j)
injective {i} {j} {A} {B} f = (a1 a2 : A) → (f a1) ≡ (f a2) → a1 ≡ a2

bijective : ∀ {i j} {A : Set i} {B : Set j} → (A → B) → Set (i ⊔ j)
bijective {i} {j} {A} {B} f = (injective f) × (surjective f)



id : ∀ {i} {A : Set i} → A → A
id {i} {A} a = a

id-injective : ∀ {i} {A : Set i} → injective (id {i} {A})
id-injective a1 a2 ida1≡ida2 = ida1≡ida2

id-surjective : ∀ {i} {A : Set i} → surjective (id {i} {A})
id-surjective a = (a , refl)

id-bijective : ∀ {i} {A : Set i} → bijective (id {i} {A})
id-bijective = (id-injective , id-surjective)


inv-strong : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → (g : B → A) → Set (i ⊔ j)
inv-strong {i} {j} {A} {B} f g = (g ∘ f ≡ id) × (f ∘ g ≡ id)

inv-weak : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → (g : B → A) → Set (i ⊔ j)
inv-weak {i} {j} {A} {B} f g = ((a : A) → (g (f a)) ≡ a) × ((b : B) → (f (g b)) ≡ b)


injectivity-refl : ∀ {i} {A : Set i} → ∃ f ∈ (A → A) , (injective f)
injectivity-refl {i} {A} = (id , id-injective)

surjectivity-refl : ∀ {i} {A : Set i} → ∃ f ∈ (A → A) , (surjective f)
surjectivity-refl {i} {A} = (id , id-surjective)

bijectivity-refl : ∀ {i} {A : Set i} → ∃ f ∈ (A → A) , (bijective f)
bijectivity-refl {i} {A} = (id , id-bijective)



surjectivity-trans : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → (f : A → B) → surjective f → (g : B → C) → surjective g → surjective (g ∘ f)
surjectivity-trans {i} {j} {k} {A} {B} {C} f f-surj g g-surj c = (a , gfa≡c)
 where
  b : B
  b = π₁ (g-surj c)

  gb≡c : (g b) ≡ c
  gb≡c = π₂ (g-surj c)

  a : A
  a = π₁ (f-surj b)

  fa≡b : (f a) ≡ b
  fa≡b = π₂ (f-surj b)

  gfa≡gb : (g (f a)) ≡ (g b)
  gfa≡gb = continuity g (f a) b fa≡b

  gfa≡c : (g (f a)) ≡ c
  gfa≡c = ≡-trans gfa≡gb gb≡c

injectivity-trans : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → (f : A → B) → injective f → (g : B → C) → injective g → injective (g ∘ f)
injectivity-trans {i} {j} {k} {A} {B} {C} f f-inj g g-inj a1 a2 gfa1≡gfa2 = a1≡a2
 where
  fa1≡fa2 : (f a1) ≡ (f a2)
  fa1≡fa2 = g-inj (f a1) (f a2) gfa1≡gfa2

  a1≡a2 : a1 ≡ a2
  a1≡a2 = f-inj a1 a2 fa1≡fa2


bijectivity-trans : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → (f : A → B) → bijective f → (g : B → C) → bijective g → bijective (g ∘ f)
bijectivity-trans {i} {j} {k} {A} {B} {C} f f-bij g g-bij = (injectivity-trans f (first f-bij) g (first g-bij) , surjectivity-trans f (second f-bij) g (second g-bij))

HEquiv : ∀ {i j} {A : Set i} {B : Set j} → (f g : A → B) → Set (i ⊔ j)
HEquiv {i} {j} {A} {B} f g = (a1 a2 : A) → (f a1) ≡ (f a2) → a1 ≡ a2

{-
General reflexivity
General irreflexivity
General transitivity
General symmetry
General antisymmetry
General asymmetry
Preorders
Partial orders
Equivalence relations
Homomorphism
Isomomorphism
Functors
Univalence
Inverses
Left-inverses
Right-inverses
Left-identities
Right-identities
Pseudo-inverses
-}

