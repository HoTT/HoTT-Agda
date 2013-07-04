{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Pi

module lib.types.Cospan where

record Cospan {i j k : ULevel} : Type (lsucc (lmax (lmax i j) k)) where
  constructor cospan
  field
    A : Type i
    B : Type j
    C : Type k
    f : A → C
    g : B → C
