module Data.Bool where

open import Agda.Primitive


data Bool : Set where
 true : Bool
 false : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

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
