{-# OPTIONS --without-K #-}

open import Base
open import Topology.Suspension

module Topology.Spheres where

-- [Sⁿ n] is the sphere of dimension (n - 1)
Sⁿ : ℕ → Set
Sⁿ O = ⊥
Sⁿ (S n) = suspension (Sⁿ n)
