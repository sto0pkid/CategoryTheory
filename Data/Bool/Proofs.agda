module Data.Bool.Proofs where

open import BaseLogic using (_≠_ ; [x≡y]→[fx≡fy] ; ⊤≠⊥)
open import Data.False
open import Data.True
open import Data.PropositionalEquality
open import Data.Bool
open import Data.Bool.Operations

𝕥≠𝕗 : true ≠ false
𝕥≠𝕗 [𝕥≡𝕗] = ☢ 
 where
  [𝕥≡𝕗]→[⊤≡⊥] : (true ≡ false) → (⊤ ≡ ⊥)
  [𝕥≡𝕗]→[⊤≡⊥] [𝕥≡𝕗] = [x≡y]→[fx≡fy] BoolProp true false [𝕥≡𝕗]

  [⊤≡⊥] : ⊤ ≡ ⊥
  [⊤≡⊥] = [𝕥≡𝕗]→[⊤≡⊥] [𝕥≡𝕗]

  ☢ : ⊥
  ☢ = ⊤≠⊥ [⊤≡⊥]

true≠false : true ≠ false
true≠false = 𝕥≠𝕗


b≡true→if[b]then[a₁]else[a₂]≡a₁ : ∀ {α} {A : Set α} → (a₁ a₂ : A) → (b : Bit) → b ≡ true → if b then a₁ else a₂ ≡ a₁
b≡true→if[b]then[a₁]else[a₂]≡a₁ {α} {A} a₁ a₂ true 𝕥≡𝕥 = refl
b≡true→if[b]then[a₁]else[a₂]≡a₁ {α} {A} a₁ a₂ false 𝕗≡𝕥 = ω (𝕥≠𝕗 (≡-↑↓ 𝕗≡𝕥))

b≡false→if[b]then[a₁]else[a₂]≡a₂ : ∀ {α} {A : Set α} → (a₁ a₂ : A) → (b : Bit) → b ≡ false → if b then a₁ else a₂ ≡ a₂
b≡false→if[b]then[a₁]else[a₂]≡a₂ {α} {A} a₁ a₂ true 𝕥≡𝕗 = ω (𝕥≠𝕗 𝕥≡𝕗)
b≡false→if[b]then[a₁]else[a₂]≡a₂ {α} {A} a₁ a₂ false 𝕗≡𝕗 = refl
