{-# OPTIONS --without-K --rewriting #-}

open import HoTT

open import stash.modalities.Orthogonality
open import stash.modalities.Modalities

module stash.modalities.Nullification where

module _ {i} where

  postulate -- HIT
    P⟨_⟩_ : (A X : Type i) → Type i
    p[_] : {A X : Type i} → X → P⟨ A ⟩ X
    is-orth : {A X : Type i} → ⟦ A ⊥ P⟨ A ⟩ X ⟧

  module NullElim {A X : Type i} {Q : P⟨ A ⟩ X → Type i}
    (p : (x : P⟨ A ⟩ X) → ⟦ A ⊥ Q x ⟧) (d : (x : X) → Q p[ x ]) where

    postulate
      f : Π (P⟨ A ⟩ X) Q
      p[_]-β : ∀ x → f p[ x ] ↦ d x
    {-# REWRITE p[_]-β #-}
    



