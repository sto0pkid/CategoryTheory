module Functions where

open import Agda.Primitive
open import Data.Irrelevance
open import Data.Nat
open import Data.Product
open import Data.PropositionalEquality
open import SetTheory

{-
Functions are continuous with respect to propositional equality.
Functions behave functorially with respect to propositional equality.
-}
continuity : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → (x y : A) → x ≡ y → (f x) ≡ (f y)
continuity {i} {j} {A} {B} f x .x refl = refl

[f≡g]→[fx≡gx] : ∀ {i j} {A : Set i} {B : Set j} → (f g : A → B) → f ≡ g → (x : A) → (f x) ≡ (g x)
[f≡g]→[fx≡gx] {i} {j} {A} {B} f .f refl x = refl

[x≡y]→[f≡g]→[fx≡gy] : ∀ {i j} {A : Set i} {B : Set j} → (x y : A) → x ≡ y → (f g : A → B) → f ≡ g → (f x) ≡ (g y)
[x≡y]→[f≡g]→[fx≡gy] {i} {j} {A} {B} x .x refl f .f refl = refl


_∘_ : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → (B → C) → (A → B) → (A → C)
(g ∘ f) a = g (f a)

∘-assoc : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {D : Set l} → (h : C → D) → (g : B → C) → (f : A → B) → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
∘-assoc {i} {j} {k} {l} {A} {B} {C} {D} h g f = refl

curry : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → (A × B → C) → (A → B → C)
curry {i} {j} {k} {A} {B} {C} f a b = f (a , b)

uncurry : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → (A → B → C) → (A × B → C)
uncurry {i} {j} {k} {A} {B} {C} f (a , b) = f a b


id : ∀ {i} {A : Set i} → A → A
id {i} {A} a = a

_^_ : ∀ {i} {A : Set i} → (A → A) → Nat → A → A
f ^ 0 = id
(f ^ (suc n)) a = f ((f ^ n) a)


surjective : ∀ {i j} {A : Set i} {B : Set j} → (A → B) → Set (i ⊔ j)
surjective {i} {j} {A} {B} f = (b : B) → ∃ a ∈ A , ((f a) ≡ b)

injective : ∀ {i j} {A : Set i} {B : Set j} → (A → B) → Set (i ⊔ j)
injective {i} {j} {A} {B} f = (a1 a2 : A) → (f a1) ≡ (f a2) → a1 ≡ a2

bijective : ∀ {i j} {A : Set i} {B : Set j} → (A → B) → Set (i ⊔ j)
bijective {i} {j} {A} {B} f = (injective f) × (surjective f)

∃surjection : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
∃surjection {i} {j} A B = ∃ f ∈ (A → B) , (surjective f)

∃injection : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
∃injection {i} {j} A B = ∃ f ∈ (A → B) , (injective f)

∃bijection : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
∃bijection {i} {j} A B = ∃ f ∈ (A → B) , (bijective f)



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

∃injection-refl : ∀ {i} {A : Set i} → ∃injection A A
∃injection-refl = injectivity-refl

surjectivity-refl : ∀ {i} {A : Set i} → ∃ f ∈ (A → A) , (surjective f)
surjectivity-refl {i} {A} = (id , id-surjective)

∃surjection-refl : ∀ {i} {A : Set i} → ∃surjection A A
∃surjection-refl = surjectivity-refl

bijectivity-refl : ∀ {i} {A : Set i} → ∃ f ∈ (A → A) , (bijective f)
bijectivity-refl {i} {A} = (id , id-bijective)

∃bijection-refl : ∀ {i} {A : Set i} → ∃bijection A A
∃bijection-refl {i} {A} = bijectivity-refl


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

∃surjection-trans : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → ∃surjection A B → ∃surjection B C → ∃surjection A C
∃surjection-trans {i} {j} {k} {A} {B} {C} (f , f-surj) (g , g-surj) = ((g ∘ f) , surjectivity-trans f f-surj g g-surj)

injectivity-trans : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → (f : A → B) → injective f → (g : B → C) → injective g → injective (g ∘ f)
injectivity-trans {i} {j} {k} {A} {B} {C} f f-inj g g-inj a1 a2 gfa1≡gfa2 = a1≡a2
 where
  fa1≡fa2 : (f a1) ≡ (f a2)
  fa1≡fa2 = g-inj (f a1) (f a2) gfa1≡gfa2

  a1≡a2 : a1 ≡ a2
  a1≡a2 = f-inj a1 a2 fa1≡fa2

∃injection-trans : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → ∃injection A B → ∃injection B C → ∃injection A C
∃injection-trans (f , f-inj) (g , g-inj) = ((g ∘ f) , injectivity-trans f f-inj g g-inj)

bijectivity-trans : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → (f : A → B) → bijective f → (g : B → C) → bijective g → bijective (g ∘ f)
bijectivity-trans {i} {j} {k} {A} {B} {C} f f-bij g g-bij = (injectivity-trans f (first f-bij) g (first g-bij) , surjectivity-trans f (second f-bij) g (second g-bij))

∃bijection-trans : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → ∃bijection A B → ∃bijection B C → ∃bijection A C
∃bijection-trans (f , f-bij) (g , g-bij) = ((g ∘ f) , bijectivity-trans f f-bij g g-bij)


∃bijection-sym : ∀ {i j} {A : Set i} {B : Set j} → ∃bijection A B → ∃bijection B A
∃bijection-sym {i} {j} {A} {B} (f , (f-inj , f-surj)) = (f⁻¹ , (f⁻¹-inj , f⁻¹-surj))
 where
  f⁻¹ : B → A
  f⁻¹ b = π₁ (f-surj b)

  f⁻¹-inj : injective f⁻¹
  f⁻¹-inj b₁ b₂ [f⁻¹-b₁≡f⁻¹-b₂] = proof
   where
    [f∘f⁻¹]b₁≡b₁ : f (f⁻¹ b₁) ≡ b₁
    [f∘f⁻¹]b₁≡b₁ = π₂ (f-surj b₁)

    [f∘f⁻¹]b₂≡b₂ : f (f⁻¹ b₂) ≡ b₂
    [f∘f⁻¹]b₂≡b₂ = π₂ (f-surj b₂)

    [f∘f⁻¹]b₁≡[f∘f⁻¹]b₂ : f (f⁻¹ b₁) ≡ f (f⁻¹ b₂)
    [f∘f⁻¹]b₁≡[f∘f⁻¹]b₂ = continuity f (f⁻¹ b₁) (f⁻¹ b₂) [f⁻¹-b₁≡f⁻¹-b₂]

    proof : b₁ ≡ b₂ 
    proof = ≡-trans (≡-sym [f∘f⁻¹]b₁≡b₁) (≡-trans [f∘f⁻¹]b₁≡[f∘f⁻¹]b₂  [f∘f⁻¹]b₂≡b₂)

  f⁻¹-surj : surjective f⁻¹
  f⁻¹-surj a = ((f a) , proof)
   where
    [f⁻¹∘f]a : A
    [f⁻¹∘f]a = f⁻¹ (f a)

    [f∘f⁻¹∘f]a : B
    [f∘f⁻¹∘f]a = f (f⁻¹ (f a))

    [f∘f⁻¹∘f]a≡[f]a : f (f⁻¹ (f a)) ≡ (f a)
    [f∘f⁻¹∘f]a≡[f]a = π₂ (f-surj (f a))

    proof : f⁻¹ (f a) ≡ a
    proof = f-inj [f⁻¹∘f]a a [f∘f⁻¹∘f]a≡[f]a



HEquiv : ∀ {i j} {A : Set i} {B : Set j} → (f g : A → B) → Set (i ⊔ j)
HEquiv {i} {j} {A} {B} f g = (a1 a2 : A) → (f a1) ≡ (f a2) → a1 ≡ a2


coerce-func-domain : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → (C : Set i) → A ≡ C → (C → B)
coerce-func-domain {i} {j} {A} {B} f .A refl = f

coerce-func-codomain : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → (C : Set j) → B ≡ C → (A → C)
coerce-func-codomain {i} {j} {A} {B} f .B refl = f

function-to-graph : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → Set (i ⊔ j)
function-to-graph {i} {j} {A} {B} f = ∃ edge ∈ (A × B) , (f (first edge) ≡ (second edge))

function-to-graph₂ : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → Set (i ⊔ j)
function-to-graph₂ {i} {j} {A} {B} f = ∃ edge ∈ (A × B) , (∥ f (first edge) ≡ (second edge) ∥ )
-- this definition is much like the first except the ∥_∥ means that we don't care to differentiate
-- the proofs of equality. this allows us to get a set with the right cardinality.

function-graph : ∀ {i j k} (A : Set i) (B : Set j) → Set (lsuc k ⊔ (i ⊔ j))
function-graph {i} {j} {k} A B = ∃ S ∈ Subset {i ⊔ j} {k} (A × B) , ((a : A) → (∃ edge ∈ (A × B) , (((first edge) ≡ a) × ((b : B) → (∃ edge₂ ∈ (A × B) , ((first edge₂ ≡ a) × (second edge₂ ≡ b))) → (second edge) ≡ b))))

{-
Preorders
Partial orders
 Injectivity and surjectivity make partial orders
Equivalence relations
 Bijectivity makes an equivalence relation
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

