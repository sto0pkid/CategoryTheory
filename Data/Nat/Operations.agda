module Data.Nat.Operations where

open import Data.Nat
open import Data.Nat.BinPreds
open import Data.Product
open import Data.Bool

data ThreeObjects : Set where
 one : ThreeObjects
 two : ThreeObjects
 three : ThreeObjects

plus : Nat → Nat → Nat
plus zero y = y
plus (suc x) y = suc (plus x y)

infixr 4 _+_
_+_ : Nat → Nat → Nat
x + y = plus x y

mult : Nat → Nat → Nat
mult zero y = zero
mult (suc x) y = plus y (mult x y)

infixr 5 _*_
_*_ : Nat → Nat → Nat
x * y = mult x y

prev : Nat → Nat
prev zero = zero
prev (suc x) = x

pred : Nat → Nat
pred x = prev x

_minus_ : Nat → Nat → Nat
zero minus y = zero
(suc x) minus zero = suc x
(suc x) minus (suc y) = x minus y

infixr 6 _^_
_^_ : Nat → Nat → Nat
x ^ zero = (suc zero)
x ^ (suc y) = x * (x ^ y)

diff : Nat → Nat → Nat
diff zero zero = zero
diff zero (suc y) = (suc y)
diff (suc x) zero = (suc x)
diff (suc x) (suc y) = diff x y

diff₂ : Nat → Nat → Nat × ThreeObjects
diff₂ zero zero = (zero , three)
diff₂ zero (suc y) = (suc y , two)
diff₂ (suc x) zero = (suc x , one)
diff₂ (suc x) (suc y) = diff₂ x y
