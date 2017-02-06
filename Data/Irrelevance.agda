module Data.Irrelevance where

record ∥_∥ {α} (A : Set α) : Set α where
 constructor squash
 field
  .x : A


{-
 Often-times we don't care which proof is given for a proposition, we
 only care whether the proposition is true. In those cases, we don't
 really care about the proposition itself, call it A, what we care about
 is Irr A.
-}
record Irr {α} {A : Set α} : Set α where
 constructor irrelefy
 field
  .x : A
