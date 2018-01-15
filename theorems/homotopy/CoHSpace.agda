{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module homotopy.CoHSpace where

record CoHSpaceStructure {i} (X : Ptd i) : Type i where
  constructor coHSpaceStructure
  field
    ⊙coμ : X ⊙→ X ⊙∨ X

  coμ : de⊙ X → X ∨ X
  coμ = fst ⊙coμ

  field
    ⊙unit-l : ⊙projr ⊙∘ ⊙coμ ⊙∼ ⊙idf X
    ⊙unit-r : ⊙projl ⊙∘ ⊙coμ ⊙∼ ⊙idf X
