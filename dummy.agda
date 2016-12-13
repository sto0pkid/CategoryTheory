module dummy where

data Nat : Set where
 zero : Nat
 suc : Nat -> Nat

f : Nat -> Nat
f x = suc (suc x)

something : Nat
something = f (f zero)
