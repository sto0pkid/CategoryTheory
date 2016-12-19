module Data.String where

open import Data.List
open import Data.Bool

postulate Char : Set
{-# BUILTIN CHAR Char #-}

postulate String : Set
{-# BUILTIN STRING String #-}

postulate primStringToList : String → List Char
postulate primStringFromList : List Char → String
postulate primStringAppend : String → String → String
postulate primStringEquality : String → String → Bool
postulate primShowString : String → String


postulate primShowChar : Char → String
