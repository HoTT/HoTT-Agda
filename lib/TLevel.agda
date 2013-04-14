{-# OPTIONS --without-K #-}

module lib.TLevel where

open import lib.Base
open import lib.Nat

data ℕ₋₂ : Type₀ where
  ⟨-2⟩ : ℕ₋₂
  S : (n : ℕ₋₂) → ℕ₋₂

⟨-1⟩ : ℕ₋₂
⟨-1⟩ = S ⟨-2⟩

⟨0⟩ : ℕ₋₂
⟨0⟩ = S ⟨-1⟩

_-1 : ℕ → ℕ₋₂
O -1 = ⟨-1⟩
(S n) -1 = S (n -1)

⟨_⟩ : ℕ → ℕ₋₂
⟨ n ⟩ = S (n -1)

⟨1⟩ = ⟨ 1 ⟩
⟨2⟩ = ⟨ 2 ⟩

_+2+_ : ℕ₋₂ → ℕ₋₂ → ℕ₋₂
⟨-2⟩ +2+ n = n
S m +2+ n = S (m +2+ n)
