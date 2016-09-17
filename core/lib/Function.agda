{-# OPTIONS --without-K #-}

open import lib.Base

module lib.Function where

{- Homotopy fibers -}
hfiber : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) (y : B) → Type (lmax i j)
hfiber {A = A} f y = Σ A (λ x → f x == y)

is-inj : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) → Type (lmax i j)
is-inj {A = A} f = ∀ (a₁ a₂ : A) → f a₁ == f a₂ → a₁ == a₂
