{-# OPTIONS --without-K #-}

open import lib.Base

module lib.Function where

{- Homotopy fibers -}
hfiber : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) (y : B) → Type (lmax i j)
hfiber {A = A} f y = Σ A (λ x → f x == y)

is-inj : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) → Type (lmax i j)
is-inj {A = A} f = ∀ (a₁ a₂ : A) → f a₁ == f a₂ → a₁ == a₂

{- maps between two functions -}

record CommSquare {i₀ i₁ j₀ j₁}
  {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
  (f₀ : A₀ → B₀) (f₁ : A₁ → B₁) (hA : A₀ → A₁) (hB : B₀ → B₁)
  : Type (lmax (lmax i₀ i₁) (lmax j₀ j₁)) where
  constructor comm-sqr
  field
    commutes : ∀ a₀ → (hB ∘ f₀) a₀ == (f₁ ∘ hA) a₀

open CommSquare public
