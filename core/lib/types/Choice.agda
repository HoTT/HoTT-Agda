{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Truncation
open import lib.types.Pi

module lib.types.Choice where

unchoose : ∀ {i j} {n : ℕ₋₂} {A : Type i} {B : A → Type j}
  → Trunc n (Π A B) → Π A (Trunc n ∘ B)
unchoose = Trunc-rec (Π-level λ _ → Trunc-level) (λ f → [_] ∘ f)

has-choice : ∀ {i} (n : ℕ₋₂) (A : Type i) j → Type (lmax i (lsucc j))
has-choice {i} n A j = (B : A → Type j) → is-equiv (unchoose {n = n} {A} {B})
