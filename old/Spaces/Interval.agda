{-# OPTIONS --without-K #-}

open import Base

module Spaces.Interval where

private
  data #I : Set where
    #zer : #I
    #one : #I

I : Set
I = #I

zer : I
zer = #zer

one : I
one = #one

postulate  -- HIT
  seg : zer ≡ one

I-rec : ∀ {i} (P : I → Set i) (x₀ : P zer) (x₁ : P one)
  (p : transport P seg x₀ ≡ x₁)
  → ((t : I) → P t)
I-rec P x₀ x₁ p #zer = x₀
I-rec P x₀ x₁ p #one = x₁

postulate  -- HIT
  β : ∀ {i} (P : I → Set i) (x₀ : P zer) (x₁ : P one)
      (p : transport P seg x₀ ≡ x₁)
      → apd (I-rec P x₀ x₁ p) seg ≡ p

I-rec-nondep : ∀ {i} (C : Set i) (x₀ x₁ : C) (p : x₀ ≡ x₁) → (I → C)
I-rec-nondep C x₀ x₁ p #zer = x₀
I-rec-nondep C x₀ x₁ p #one = x₁

postulate  -- HIT
  β-nondep : ∀ {i} (C : Set i) (x₀ x₁ : C) (p : x₀ ≡ x₁)
             → ap (I-rec-nondep C x₀ x₁ p) seg ≡ p
