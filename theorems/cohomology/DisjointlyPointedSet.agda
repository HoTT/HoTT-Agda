{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.Bouquet
open import homotopy.DisjointlyPointedSet
open import cohomology.Theory

module cohomology.DisjointlyPointedSet {i} (OT : OrdinaryTheory i) where

  open OrdinaryTheory OT
  open import cohomology.Bouquet OT

  module _ (X : Ptd i)
    (X-is-set : is-set (de⊙ X)) (X-sep : is-separable X)
    (ac : has-choice 0 (de⊙ X) i) where

    C-set : C 0 X ≃ᴳ Πᴳ (MinusPoint X) (λ _ → C2 0)
    C-set = C-Bouquet-diag 0 (MinusPoint X) (MinusPoint-has-choice 0 X-sep ac)
        ∘eᴳ C-emap 0 (Bouquet-⊙equiv-X X-sep)

  module _ {n : ℤ} (n≠0 : n ≠ 0) (X : Ptd i)
    (X-is-set : is-set (de⊙ X)) (X-sep : is-separable X)
    (ac : has-choice 0 (de⊙ X) i) where

    abstract
      C-set-≠-is-trivial : is-trivialᴳ (C n X)
      C-set-≠-is-trivial = iso-preserves'-trivial
        (C-emap n (Bouquet-⊙equiv-X X-sep))
        (C-Bouquet-≠-is-trivial n (MinusPoint X) 0 n≠0 (MinusPoint-has-choice 0 X-sep ac))
