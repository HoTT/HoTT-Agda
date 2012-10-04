{-# OPTIONS --without-K #-}

module Spaces.Spheres where

open import Base
open import Spaces.Suspension public

-- [Sⁿ n] is the sphere of dimension (n - 1)
Sⁿ : ℕ → Set
Sⁿ O = ⊥
Sⁿ (S n) = suspension (Sⁿ n)
