{-# OPTIONS --without-K #-}

open import Base

module Spaces.WedgeCircles {i} (A : Set i) where

{-
The idea is

data wedge-circles : Set (suc i) where
  base : wedge-circles
  loops : A → base ≡ base
-}

private
  data #wedge-circles : Set (suc i) where
    #base : #wedge-circles

wedge-circles : Set (suc i)
wedge-circles = #wedge-circles

base : wedge-circles
base = #base

postulate  -- HIT
  loops : A → base ≡ base

wedge-circles-rec : ∀ {i} (P : wedge-circles → Set i) (x : P base)
  (p : (t : A) → transport P (loops t) x ≡ x) → ((t : wedge-circles) → P t)
wedge-circles-rec P x p #base = x

postulate  -- HIT
  β : ∀ {i} (P : wedge-circles → Set i) (x : P base)
      (p : (t : A) → transport P (loops t) x ≡ x) (t : A)
      → map-dep (wedge-circles-rec P x p) (loops t) ≡ p t

wedge-circles-rec-nondep : ∀ {i} (B : Set i) (x : B) (p : A → x ≡ x)
  → (wedge-circles → B)
wedge-circles-rec-nondep B x p #base = x
--  wedge-circles-rec (λ _ → B) x (λ t → trans-A (loops t) x ∘ p t)

postulate  -- HIT
  β-nondep : ∀ {i} (B : Set i) (x : B) (p : A → x ≡ x) (t : A)
      → map (wedge-circles-rec-nondep B x p) (loops t) ≡ p t

-- abstract
--   β-nondep : ∀ {i} (B : Set i) (x : B) (p : A → x ≡ x) (t : A)
--     → map (wedge-circles-rec-nondep B x p) (loops t) ≡ p t
--   β-nondep B x p t = map-dep-trivial (wedge-circles-rec-nondep B x p) (loops t)
--     ∘ (whisker-left (! (trans-A (loops t) x)) (β (λ _ → B) _ _ _)
--     ∘ (! (concat-assoc (! (trans-A (loops t) x)) (trans-A (loops t) x) _)
--     ∘ whisker-right (p t) (opposite-left-inverse (trans-A (loops t) x))))
