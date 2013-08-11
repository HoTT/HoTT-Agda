{-# OPTIONS --without-K #-}

open import lib.Basics

module lib.types.Lift where

lift-equiv : ∀ {i j} {A : Type i} → Lift {j = j} A ≃ A
lift-equiv = equiv lower lift (λ _ → idp) (λ _ → idp)

Lift-level : ∀ {i j} {A : Type i} {n : ℕ₋₂} → 
  has-level n A → has-level n (Lift {j = j} A)
Lift-level = equiv-preserves-level ((lift-equiv)⁻¹)