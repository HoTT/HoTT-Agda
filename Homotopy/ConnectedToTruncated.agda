{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Truncation
open import Homotopy.Connected

module Homotopy.ConnectedToTruncated {i j} (X : Set i) (Y : Set j) (n : ℕ₋₂)
  (p : is-connected n X) (x₀ : X) (q : is-truncated n Y) where

{- We want to prove [Y ≃ X → Y] -}

private
  app : (X → Y) → Y
  app f = f x₀

  app-cst : (y : Y) → app (cst y) ≡ y
  app-cst y = refl y

  cst-app : (f : X → Y) → cst (app f) ≡ f
  cst-app f = funext (λ x → eq' (proj x)) where
    f' : τ n X → Y
    f' = τ-extend-nondep f

    x'₀ : τ n X
    x'₀ = proj x₀

    eq' : (x : τ n X) → f' x'₀ ≡ f' x
    eq' x = transport (λ y → f' x'₀ ≡ f' y) (π₂ p x'₀ ∘ ! (π₂ p x)) (refl _)

app-is-inj : (f g : X → Y) (p : f x₀ ≡ g x₀) → f ≡ g
app-is-inj f g p = ! (cst-app f) ∘ (map cst p ∘ cst-app g)
