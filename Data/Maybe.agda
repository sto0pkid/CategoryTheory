module Data.Maybe where

data Maybe {α} (A : Set α) : Set α where
 Nothing : Maybe A
 Just : A → Maybe A
