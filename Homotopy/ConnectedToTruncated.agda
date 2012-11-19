{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Truncation
open import Homotopy.Connected

module Homotopy.ConnectedToTruncated {i j} (X : Set i) (Y : Set j) (n : ℕ₋₂)
  (p : is-connected n X) (q : is-truncated n Y) where

app-is-inj : (x₀ : X) (f g : X → Y) (p : f x₀ ≡ g x₀) → f ≡ g
app-is-inj x₀ f g q = equiv-is-inj (τ-extend-equiv n X Y) f g
                                   (funext (contr-has-section p (proj x₀) q))