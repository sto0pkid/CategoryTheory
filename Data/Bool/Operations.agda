module Data.Bool.Operations where

open import Data.False
open import Data.True
open import Data.Bool

BoolProp : Bool → Set
BoolProp true = ⊤
BoolProp false = ⊥

BoolToSet : Bool → Set
BoolToSet true = ⊤
BoolToSet false = ⊥


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

_xor_ : Bool → Bool → Bool
true xor true = false
true xor false = true
false xor true = true
false xor false = false

if_then_else : ∀ {α} {A : Set α} → Bool → A → A → A
if_then_else true x y = x
if_then_else false x y = y
