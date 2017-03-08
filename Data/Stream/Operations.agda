module Data.Stream.Operations where

open import Data.Prim.Coinduction
open import Data.Stream

head : ∀ {i} {A : Set i} → Stream A → A
head {i} {A} (a ∷ as) = a

head∞ : ∀ {i} {A : Set i} → ∞ (Stream A) → A
head∞ {i} {A} s = head (♭ s)

∞tail : ∀ {i} {A : Set i} → Stream A → ∞ (Stream A)
∞tail {i} {A} (a ∷ as) = as

tail : ∀ {i} {A : Set i} → Stream A → Stream A
tail {i} {A} (a ∷ as) = ♭ as

∞tail∞ : ∀ {i} {A : Set i} → ∞ (Stream A) → ∞ (Stream A)
∞tail∞ {i} {A} s = ∞tail (♭ s)

tail∞ : ∀ {i} {A : Set i} → ∞ (Stream A) → Stream A
tail∞ {i} {A} s = tail (♭ s)

map : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → Stream A → Stream B
map {i} {j} {A} {B} f (a ∷ as) = (f a) ∷ (♯ (map f (♭ as)))

∞map : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → ∞ (Stream A) → Stream B
∞map {i} {j} {A} {B} f s = map f (♭ s)

map∞ : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → Stream A → ∞ (Stream B)
map∞ {i} {j} {A} {B} f s = ♯ (map f s)

∞map∞ : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → ∞ (Stream A) → ∞ (Stream B)
∞map∞ {i} {j} {A} {B} f s = map∞ f (♭ s) 
