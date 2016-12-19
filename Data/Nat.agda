module Data.Nat where

data Nat : Set where
 zero : Nat
 suc : Nat → Nat

{-# BUILTIN NATURAL Nat #-}
