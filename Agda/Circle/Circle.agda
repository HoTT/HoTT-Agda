{-# OPTIONS --without-K #-}

open import Homotopy

module Circle.Circle where

{-
Idea :

data circle : Set₁ where
  base : circle
  loop : base ≡ base

I’m using Dan Licata’s trick to have a higher inductive type with definitional reduction rule for [base]
-}

private
  data #circle : Set where
    #base : #circle

circle : Set
circle = #circle

base : circle
base = #base

postulate  -- HIT
  loop : base ≡ base

circle-rec : ∀ {i} (P : circle → Set i) (x : P base) (p : transport P loop x ≡ x) → ((t : circle) → P t)
circle-rec P x p #base = x

postulate  -- HIT
  β : ∀ {i} (P : circle → Set i) (x : P base) (p : transport P loop x ≡ x)
      → map-dep (circle-rec P x p) loop ≡ p

circle-rec-nondep : ∀ {i} (A : Set i) (x : A) (p : x ≡ x) → (circle → A)
circle-rec-nondep A x p = circle-rec (λ _ → A) x (trans-A loop x ∘ p)

β-nondep : ∀ {i} (A : Set i) (x : A) (p : x ≡ x) → map (circle-rec-nondep A x p) loop ≡ p
β-nondep A x p = map-dep-trivial (circle-rec-nondep A x p) loop ∘ (whisker-left (! (trans-A loop _)) (β (λ _ → A) x (trans-A loop _ ∘ p))
  ∘ (! (concat-assoc (! (trans-A loop _)) (trans-A loop _) p)
  ∘ whisker-right p (opposite-left-inverse (trans-A loop _))))