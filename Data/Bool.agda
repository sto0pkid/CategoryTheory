module Data.Bool where

open import Agda.Primitive


data Bool : Set where
 true : Bool
 false : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

if_then_else : ∀ {α} {A : Set α} → Bool → A → A → A
if_then_else true x y = x
if_then_else false x y = y
