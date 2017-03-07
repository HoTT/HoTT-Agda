{-# OPTIONS --without-K --rewriting #-}

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

record ⊙Cospan {i j k : ULevel} : Type (lsucc (lmax (lmax i j) k)) where
  constructor ⊙cospan
  field
    X : Ptd i
    Y : Ptd j
    Z : Ptd k
    f : X ⊙→ Z
    g : Y ⊙→ Z

⊙cospan-out : ∀ {i j k} → ⊙Cospan {i} {j} {k} → Cospan {i} {j} {k}
⊙cospan-out (⊙cospan X Y Z f g) =
  cospan (de⊙ X) (de⊙ Y) (de⊙ Z) (fst f) (fst g)
