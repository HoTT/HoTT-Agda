{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Pi
open import lib.types.Pointed

module lib.types.Cospan where

record Cospan {i j k : ULevel} : Type (lsucc (lmax (lmax i j) k)) where
  constructor cospan
  field
    A : Type i
    B : Type j
    C : Type k
    f : A → C
    g : B → C

record Ptd-Cospan {i j k : ULevel} : Type (lsucc (lmax (lmax i j) k)) where
  constructor ptd-cospan
  field
    X : Ptd i
    Y : Ptd j
    Z : Ptd k
    f : fst (X ∙→ Z)
    g : fst (Y ∙→ Z)

ptd-cospan-out : ∀ {i j k} → Ptd-Cospan {i} {j} {k} → Cospan {i} {j} {k}
ptd-cospan-out (ptd-cospan X Y Z f g) = 
  cospan (fst X) (fst Y) (fst Z) (fst f) (fst g)
