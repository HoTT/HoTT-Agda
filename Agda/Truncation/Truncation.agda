{-# OPTIONS --without-K #-}

open import Base
open import Topology.Spheres

module Truncation.Truncation {i} (n : ℕ) (A : Set i) where

private
  data #τ : Set i where
    #proj : A → #τ
    #top : (f : Sⁿ n → #τ) → #τ

τ : Set i
τ = #τ

proj : A → τ
proj = #proj

top : (f : Sⁿ n → τ) → τ
top = #top

postulate  -- HIT
  rays : (f : Sⁿ n → τ) (x : Sⁿ n) → top f ≡ f x

τ-rec : ∀ {j} (P : τ → Set j)
  (proj* : (x : A) → P (proj x))
  (top* : (f : Sⁿ n → τ) (p : (x : Sⁿ n) → P (f x)) → P (top f))
  (rays* : (f : Sⁿ n → τ) (p : (x : Sⁿ n) → P (f x)) (x : Sⁿ n) → transport P (rays f x) (top* f p) ≡ p x)
  → ((x : τ) → P x)
τ-rec P proj* top* rays* (#proj u) = proj* u
τ-rec P proj* top* rays* (#top f) = top* f (λ x → τ-rec P proj* top* rays* (f x))

τ-rec-nondep : ∀ {j} (C : Set j)
  (proj* : A → C)
  (top* : (p : Sⁿ n → C) → C)
  (rays* : (p : Sⁿ n → C) (x : Sⁿ n) → top* p ≡ p x)
  → (τ → C)
τ-rec-nondep C proj* top* rays* (#proj u) = proj* u
τ-rec-nondep C proj* top* rays* (#top f) = top* (λ x → τ-rec-nondep C proj* top* rays* (f x))

-- Computation rules for [rays] are not needed
