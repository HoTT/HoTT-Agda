{-# OPTIONS --without-K #-}

open import Base

module Spaces.Circle where

{-
Idea :

data S¹ : Set where
  base : S¹
  loop : base ≡ base

I’m using Dan Licata’s trick to have a higher inductive type with definitional
reduction rule for [base]
-}

private
  data #S¹ : Set where
    #base : #S¹

S¹ : Set
S¹ = #S¹

base : S¹
base = #base

postulate  -- HIT
  loop : base ≡ base

S¹-rec : ∀ {i} (P : S¹ → Set i) (x : P base) (p : transport P loop x ≡ x)
  → ((t : S¹) → P t)
S¹-rec P x p #base = x

postulate  -- HIT
  β : ∀ {i} (P : S¹ → Set i) (x : P base) (p : transport P loop x ≡ x)
      → map-dep (S¹-rec P x p) loop ≡ p

S¹-rec-nondep : ∀ {i} (A : Set i) (x : A) (p : x ≡ x) → (S¹ → A)
S¹-rec-nondep A x p = S¹-rec (λ _ → A) x (trans-A loop x ∘ p)

β-nondep : ∀ {i} (A : Set i) (x : A) (p : x ≡ x)
  → map (S¹-rec-nondep A x p) loop ≡ p
β-nondep A x p =
  map-dep-trivial (S¹-rec-nondep A x p) loop ∘
  (whisker-left (! (trans-A loop _)) (β (λ _ → A) x (trans-A loop _ ∘ p))
  ∘ (! (concat-assoc (! (trans-A loop _)) (trans-A loop _) p)
  ∘ whisker-right p (opposite-left-inverse (trans-A loop _))))
