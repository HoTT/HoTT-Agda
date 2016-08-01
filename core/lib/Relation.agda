{-# OPTIONS --without-K #-}

open import lib.Base

module lib.Relation where

Rel : ∀ {i} (A : Type i) j → Type (lmax i (lsucc j))
Rel A j = A → A → Type j

Decidable : ∀ {i} {A : Type i} {j} → Rel A j → Type (lmax i j)
Decidable rel = ∀ a₁ a₂ → Dec (rel a₁ a₂)
