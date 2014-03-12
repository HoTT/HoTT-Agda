{-# OPTIONS --without-K #-}

open import lib.Basics

module lib.types.Lift where

Lift-level : ∀ {i j} {A : Type i} {n : ℕ₋₂} → 
  has-level n A → has-level n (Lift {j = j} A)
Lift-level = equiv-preserves-level ((lift-equiv)⁻¹)
