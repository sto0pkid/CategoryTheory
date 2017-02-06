module Data.Bool where

data Bool : Set where
 true : Bool
 false : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}


Bit : Set
Bit = Bool

