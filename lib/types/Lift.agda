{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Pointed

module lib.types.Lift where

Ptd-Lift : ∀ {i j} → Ptd i → Ptd (lmax i j)
Ptd-Lift {j = j} (A , a) = ∙[ Lift {j = j} A , lift a ]

Lift-level : ∀ {i j} {A : Type i} {n : ℕ₋₂} → 
  has-level n A → has-level n (Lift {j = j} A)
Lift-level = equiv-preserves-level ((lift-equiv)⁻¹)
