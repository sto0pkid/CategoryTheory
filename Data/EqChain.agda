module Data.EqChain where

open import Data.PropositionalEquality

infixr 3 _∷_
data EqChain {α} {A : Set α} : A → A → Set α where
 end : {x y : A} → x ≡ y → EqChain x y
 _∷_ : {x y z : A} → x ≡ y → EqChain y z → EqChain x z
 

EqChainExtract : ∀ {α} {A : Set α} {x y : A} → EqChain x y → x ≡ y
EqChainExtract {α} {A} {x} {y} (end p) = p
EqChainExtract {α} {A} {x} {y} (p ∷ (end q)) = ≡-⇶ p q
EqChainExtract {α} {A} {x} {y} (p ∷ (q ∷ rest)) = ≡-⇶ p (≡-⇶ q (EqChainExtract rest))
