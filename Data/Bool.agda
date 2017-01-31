module Data.Bool where

open import Agda.Primitive
open import BaseLogic

data Bool : Set where
 true : Bool
 false : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

BoolProp : Bool → Set
BoolProp true = ⊤
BoolProp false = ⊥

not : Bool → Bool
not true = false
not false = true

_or_ : Bool → Bool → Bool
true or true = true
true or false = true
false or true = true
false or false = false

_and_ : Bool → Bool → Bool
true and true = true
true and false = false
false and true = false
false and false = false

if_then_else : ∀ {α} {A : Set α} → Bool → A → A → A
if_then_else true x y = x
if_then_else false x y = y

𝕥≠𝕗 : true ≠ false
𝕥≠𝕗 [𝕥≡𝕗] = ☢ 
 where
  [𝕥≡𝕗]→[⊤≡⊥] : (true ≡ false) → (⊤ ≡ ⊥)
  [𝕥≡𝕗]→[⊤≡⊥] [𝕥≡𝕗] = [x≡y]→[fx≡fy] BoolProp true false [𝕥≡𝕗]

  [⊤≡⊥] : ⊤ ≡ ⊥
  [⊤≡⊥] = [𝕥≡𝕗]→[⊤≡⊥] [𝕥≡𝕗]

  ☢ : ⊥
  ☢ = ⊤≠⊥ [⊤≡⊥]
