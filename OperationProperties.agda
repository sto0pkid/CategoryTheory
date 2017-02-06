module OperationProperties where

open import Agda.Primitive
open import Data.Product
open import Data.PropositionalEquality

isAssociative : ∀ {α} {A : Set α} (+ : A → A → A) → Set α
isAssociative {a} {A} +' = (a b c : A) → a + (b + c) ≡ (a + b) + c
 where
  _+_ : A → A → A
  _+_ = +'

isCommutative : ∀ {α} {A : Set α} (+ : A → A → A) → Set α
isCommutative {α} {A} +' = (a b : A) → a + b ≡ b + a
 where
  _+_ : A → A → A
  _+_ = +'

_isLeftIdentityFor_ : ∀ {α} {A : Set α} (e : A) → (+ : A → A → A) → Set α
_isLeftIdentityFor_ {α} {A} e +' = (a : A) → e + a ≡ a
 where
  _+_ : A → A → A
  _+_ = +'

hasLeftIdentity : ∀ {α} {A : Set α} (+ : A → A → A) → Set α
hasLeftIdentity {α} {A} + = ∃ e ∈ A , (e isLeftIdentityFor +)

_isRightIdentityFor_ : ∀ {α} {A : Set α} (e : A) → (+ : A → A → A) → Set α
_isRightIdentityFor_ {α} {A} e +' = (a : A) → a + e ≡ a
 where
  _+_ : A → A → A
  _+_ = +'

hasRightIdentity : ∀ {α} {A : Set α} (+ : A → A → A) → Set α
hasRightIdentity {α} {A} + = ∃ e ∈ A , (e isRightIdentityFor +)

_isIdentityFor_ : ∀ {α} {A : Set α} (e : A) → (+ : A → A → A) → Set α
_isIdentityFor_ {α} {A} e + = (e isLeftIdentityFor +) ∧ (e isRightIdentityFor +)

hasIdentity : ∀ {α} {A : Set α} (+ : A → A → A) → Set α
hasIdentity {α} {A} + = ∃ e ∈ A , (e  isIdentityFor +)

record SemiMonoid {ℓ} : Set (lsuc ℓ) where
 field
  M : Set ℓ
  _+_ : M → M → M
  +-exid : hasIdentity _+_

[in_]_isLeftInverseOf_ : ∀ {α} (M : SemiMonoid {α}) → (x⁻¹ x : SemiMonoid.M M) → Set α
[in M' ] x⁻¹ isLeftInverseOf x = x⁻¹ + x ≡ e
 where
  M = SemiMonoid.M M'

  _+_ : M → M → M
  _+_ = SemiMonoid._+_ M'

  e : M
  e = π₁ (SemiMonoid.+-exid M')

[in_]_isRightInverseOf_ : ∀ {α} (M : SemiMonoid {α}) → (x⁻¹ x : SemiMonoid.M M) → Set α
[in M' ] x⁻¹ isRightInverseOf x = x + x⁻¹ ≡ e
 where
  M = SemiMonoid.M M'

  _+_ : M → M → M
  _+_ = SemiMonoid._+_ M'

  e : M
  e = π₁ (SemiMonoid.+-exid M')

[in_]_isInverseOf_ : ∀ {α} (M : SemiMonoid {α}) → (x⁻¹ x : SemiMonoid.M M) → Set α
[in M' ] x⁻¹ isInverseOf x = ([in M' ] x⁻¹ isLeftInverseOf x) ∧ ([in M' ] x⁻¹ isRightInverseOf x)

hasInverses : ∀ {α} (M : SemiMonoid {α}) → Set α
hasInverses {α} M' = (x : M) → ∃ x⁻¹ ∈ M , ([in M' ] x⁻¹ isInverseOf x)
 where
  M = SemiMonoid.M M'

[in_]_leftDistributesOver : ∀ {α} (A : Set α) → (* + : A → A → A) → Set α
[in A ] *' leftDistributesOver +' = (a b c : A) → a * (b + c) ≡ (a * b) + (a * c)
 where
  _*_ : A → A → A
  _*_ = *'

  _+_ : A → A → A
  _+_ = +'

[in_]_rightDistributesOver : ∀ {α} (A : Set α) → (* + : A → A → A) → Set α
[in A ] *' rightDistributesOver +' = (a b c : A) → (a + b) * c ≡ (a * c) + (b * c)
 where
  _*_ : A → A → A
  _*_ = *'

  _+_ : A → A → A
  _+_ = +'

[in_]_distributesOver : ∀ {α} (A : Set α) → (* + : A → A → A) → Set α
[in A ] * distributesOver + = ([in A ] * leftDistributesOver +) ∧ ([in A ] * rightDistributesOver +)
