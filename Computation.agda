module Computation where

open import Data.Prim.Coinduction
open import Data.Bool
open import Data.Bool.Operations
open import Data.False
open import Data.Fin
open import Data.Nat
open import Data.Nat.Operations
open import Data.Nat.Relations
open import Data.Stream
open import Data.Product
open import Data.PropositionalEquality
import Data.Stream.Operations as StreamOps
open import Data.Vector
open import Functions renaming (_^_ to _^^_)

Memory : (n : Nat) → Set
Memory n = Vector Bool n

CPU : (n : Nat) → Set
CPU n = Memory n → Memory n

ExecutionTrace : {n : Nat} → (cpu : CPU n) → (start : Memory n) → Stream (Memory n)
ExecutionTrace {n} cpu start = start ∷ (♯ (ExecutionTrace cpu (cpu start)))

all-zeroes : (n : Nat) → Memory n
all-zeroes 0 = []
all-zeroes (suc n) = false ∷ (all-zeroes n)

my-CPU : CPU 256
my-CPU (a ∷ as) = (not a) ∷ as

my-mem-config : Memory 256
my-mem-config = all-zeroes 256

my-trace : Stream (Memory 256)
my-trace = ExecutionTrace my-CPU my-mem-config

{-# NON_TERMINATING #-}
loop : Stream (Memory 256) → ⊥
loop state = loop (StreamOps.tail state)

{-# NON_TERMINATING #-}
main : ⊥
main = loop my-trace


{-
How should `main` be compiled if `my-CPU` actually models my CPU?
If `my-CPU` actually models my CPU, then `my-trace` is the stream of
states that my CPU will go through when starting in the memory configuration
`my-mem-config`. `main` is a non-terminating computation that actually
goes through each state. We can make my CPU do that by initializing my
memory configuration to `my-mem-config`.
-}

{-
CPU-attractors : {n : Nat} → (cpu : CPU n) → (state : Memory n) → ∃ k ∈ Nat , (∃ r ∈ Nat , ((k ≤ (2 ^ n)) ∧ (k > 0) ∧ (r ≤ (2 ^ n)) ∧ (r > 0) ∧ ((m : Nat) → ((cpu ^^ (k + (m * r))) state) ≡ ((cpu ^^ k) state))))
CPU-attractors {n} cpu state = proof 
 where
  proof   
-}
