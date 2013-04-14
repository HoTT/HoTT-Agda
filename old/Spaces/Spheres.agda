{-# OPTIONS --without-K #-}

module Spaces.Spheres where

open import Base
open import Spaces.Suspension public

-- [Sⁿ n] is the sphere of dimension n
Sⁿ : ℕ → Set
Sⁿ 0 = bool
Sⁿ (S n) = suspension (Sⁿ n)

⋆Sⁿ : (n : ℕ) → Sⁿ n
⋆Sⁿ 0 = true
⋆Sⁿ (S n) = north (Sⁿ n)