{-# OPTIONS --without-K #-}

open import Base
open import Truncation.TruncatedHIT

module Truncation.Truncation {i} (n : ℕ) ⦃ >0 : n ≢ 0 ⦄ (A : Set i) where

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

#τ-rec : ∀ {j} (P : τ → Set j)
  (proj* : (x : A) → P (proj x))
  (top* : (f : Sⁿ n → τ) (p : (x : Sⁿ n) → P (f x)) → P (top f))
  (rays* : (f : Sⁿ n → τ) (p : (x : Sⁿ n) → P (f x)) (x : Sⁿ n)
    → transport P (rays f x) (top* f p) ≡ p x)
  → ((x : τ) → P x)
#τ-rec P proj* top* rays* (#proj u) = proj* u
#τ-rec P proj* top* rays* (#top f) =
  top* f (λ x → #τ-rec P proj* top* rays* (f x))

#τ-rec-nondep : ∀ {j} (C : Set j)
  (proj* : A → C)
  (top* : (f : Sⁿ n → τ) (p : Sⁿ n → C) → C)
  (rays* : (f : Sⁿ n → τ) (p : Sⁿ n → C) (x : Sⁿ n) → top* f p ≡ p x)
  → (τ → C)
#τ-rec-nondep C proj* top* rays* (#proj u) = proj* u
#τ-rec-nondep C proj* top* rays* (#top f) =
  top* f (λ x → #τ-rec-nondep C proj* top* rays* (f x))

-- Computation rules for [rays] are not needed

τ-rec :  ∀ {j} (P : τ → Set j)
  (proj* : (x : A) → P (proj x))
  (trunc : (x : τ) → is-hlevel n (P x))
  → ((x : τ) → P x)
τ-rec P proj* trunc =
  #τ-rec P proj* (λ f p₁ → π₁ (u f p₁))
                 (λ f p₁ → π₂ (u f p₁)) where
  u : _
  u = hlevel-n-has-filling-dep τ P n (λ f → (top f , rays f))

τ-rec-nondep : ∀ {j} (C : Set j)
  (proj* : A → C)
  (trunc : is-hlevel n C)
  → (τ → C)
τ-rec-nondep C proj* trunc =
  #τ-rec-nondep C proj* (λ _ p → π₁ (u p))
                        (λ _ p → π₂ (u p)) where
  u : _
  u = hlevel-n-has-n-spheres-filled n _ trunc

-- The nth truncation is of h-level [n]
abstract
  τ-hlevel : is-hlevel n τ
  τ-hlevel = n-spheres-filled-hlevel n τ (λ f → (top f , rays f))
