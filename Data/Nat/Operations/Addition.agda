module Data.Nat.Operations.Addition where

open import BaseLogic using (_≠_ ; [x≡y]→[fx≡fy] ; ≠-↑↓)
open import Data.Bool
open import Data.Bool.Proofs
open import Data.Nat
open import Data.Nat.Operations
open import Data.Nat.BinPreds
open import Data.False
open import Data.PropositionalEquality

𝕤x≠𝕫 : (x : Nat) → (suc x ≠ zero)
𝕤x≠𝕫 x [𝕤x≡𝕫] = ☢
 where
  [𝕥≡isZero-𝕫] : true ≡ isZero zero
  [𝕥≡isZero-𝕫] = refl

  [isZero-𝕤x≡𝕗] : isZero (suc x) ≡ false
  [isZero-𝕤x≡𝕗] = refl

  [isZero-𝕫≡isZero-𝕤x] : isZero zero ≡ isZero (suc x)
  [isZero-𝕫≡isZero-𝕤x] = [x≡y]→[fx≡fy] isZero zero (suc x) (≡-↑↓ [𝕤x≡𝕫])

  [𝕥≡𝕗] : true ≡ false
  [𝕥≡𝕗] = ≡-⇶ (≡-⇶ [𝕥≡isZero-𝕫] [isZero-𝕫≡isZero-𝕤x]) [isZero-𝕤x≡𝕗]

  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [𝕥≡𝕗] 

𝕫≠𝕤x : (x : Nat) → (zero ≠ suc x)
𝕫≠𝕤x x = ≠-↑↓ (𝕤x≠𝕫 x)



-- 2) suc is an injection
[𝕤x≡𝕤y]→[x≡y] : (x y : Nat) → (suc x) ≡ (suc y) → x ≡ y
[𝕤x≡𝕤y]→[x≡y] x y [𝕤x≡𝕤y] = [x≡y]→[fx≡fy] prev (suc x) (suc y) [𝕤x≡𝕤y]


-- 3) prev 𝕤n ≡ n
pred-𝕤n≡n : (n : Nat) → prev (suc n) ≡ n
pred-𝕤n≡n n = refl

-- 8) (𝕤 x) + y ≡ 𝕤 (x + y)
𝕤x+y≡𝕤[x+y] : (x y : Nat) → plus (suc x) y ≡ suc (plus x y)
𝕤x+y≡𝕤[x+y] x y = refl

𝕤[x+y]≡𝕤x+y : (x y : Nat) → suc (plus x y) ≡ plus (suc x) y
𝕤[x+y]≡𝕤x+y x y = refl




