{-# OPTIONS --without-K #-}

open import Base
open import Integers
open import Homotopy.Truncation
open import Spaces.Spheres
open import Spaces.Suspension
open import Homotopy.Connected
open import Homotopy.ConnectedSuspension
open import Homotopy.Pointed
open import Homotopy.HomotopyGroups

module Spaces.PikSn where

abstract
  Sⁿ-S-is-connected : (n : ℕ) → is-connected ⟨ n ⟩ (Sⁿ (S n))
  Sⁿ-S-is-connected n =
    suspension-is-connected-S (Sⁿ n) ind-hyp (proj (⋆Sⁿ n)) where
      ind-hyp : is-connected (n -1) (Sⁿ n)
      ind-hyp with n
      ind-hyp | O = inhab-prop-is-contr (proj true) (τ-is-truncated _ _)
      ind-hyp | S n = Sⁿ-S-is-connected n

Sⁿ⋆ : (n : ℕ) → pType₀
Sⁿ⋆ n = (Sⁿ n , ⋆Sⁿ n)

abstract
  πk-Sⁿ-is-contr : (k n : ℕ) (lt : k < n)
    → is-contr⋆ (πⁿ k (Sⁿ⋆ n))
  πk-Sⁿ-is-contr k O ()
  πk-Sⁿ-is-contr k (S n) lt = connected-πⁿ k n lt _ (Sⁿ-S-is-connected n)
