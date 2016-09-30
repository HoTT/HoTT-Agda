{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Truncation
open import lib.types.Pi

module lib.types.Choice where

unchoose : ∀ {i j} {n : ℕ₋₂} {A : Type i} {B : A → Type j}
  → Trunc n (Π A B) → Π A (Trunc n ∘ B)
unchoose = Trunc-rec (Π-level (λ _ → Trunc-level)) (λ f → [_] ∘ f)

has-choice : ∀ {i j} (n : ℕ₋₂) (A : Type i) (B : A → Type j) → Type (lmax i j)
has-choice {i} {j} n A B = is-equiv (unchoose {n = n} {A} {B})
