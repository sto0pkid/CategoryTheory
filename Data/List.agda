module Data.List where

open import Agda.Primitive
--open import BaseLogic
--open import Data.Bool

infixr 3 _∷_
data List {α} (A : Set α) : Set α where
 [] : List A
 _∷_ : A → List A → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL []    #-}
{-# BUILTIN CONS _∷_  #-}

