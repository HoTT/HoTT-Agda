{-# OPTIONS --without-K #-}

open import Base

{-
  This interface is inspired by
  Haskell typeclass Applicative.
-}

module Algebra.Applicative where

record Applicative {i j} (F : Set i → Set j) : Set (max (suc i) j) where
  constructor applicative
  field
    pure : ∀ {A} → A → F A
    _✭_ : ∀ {A B} → F (A → B) → F A → F B
    {- other rules:
      pure id ✭ v ≡ v 
      pure _∘_ ✭ u ✭ v ✭ w ≡ u ✭ (v ✭ w) 
      pure f ✭ pure x ≡ pure (f x) 
      u ✭ pure y ≡ pure (λ f → f y) ✭ u 
    -}

  infixl 1 _✭_

  liftA₂ : ∀ {A B C} → F (A → B → C) → F A → F B → F C
  liftA₂ f x y = f ✭ x ✭ y
