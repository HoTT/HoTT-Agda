{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.types.Nat

module lib.types.TLevel where

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
