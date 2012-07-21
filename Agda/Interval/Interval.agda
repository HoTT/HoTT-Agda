{-# OPTIONS --without-K #-}

open import Base

module Interval.Interval where

private
  data #I : Set where
    #zero : #I
    #one : #I

I : Set
I = #I

zero : I
zero = #zero

one : I
one = #one

postulate  -- HIT
  seg : zero ≡ one

I-rec : ∀ {i} (P : I → Set i) (x₀ : P zero) (x₁ : P one) (p : transport P seg x₀ ≡ x₁)
  → ((t : I) → P t)
I-rec P x₀ x₁ p #zero = x₀
I-rec P x₀ x₁ p #one = x₁

postulate  -- HIT
  β : ∀ {i} (P : I → Set i) (x₀ : P zero) (x₁ : P one) (p : transport P seg x₀ ≡ x₁)
      → map-dep (I-rec P x₀ x₁ p) seg ≡ p

I-rec-nondep : ∀ {i} (C : Set i) (x₀ x₁ : C) (p : x₀ ≡ x₁) → (I → C)
I-rec-nondep C x₀ x₁ p #zero = x₀
I-rec-nondep C x₀ x₁ p #one = x₁

postulate  -- HIT
  β-nondep : ∀ {i} (C : Set i) (x₀ x₁ : C) (p : x₀ ≡ x₁)
             → map (I-rec-nondep C x₀ x₁ p) seg ≡ p