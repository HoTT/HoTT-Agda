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
  S¹-β-loop : ∀ {i} (P : S¹ → Set i) (x : P base) (p : transport P loop x ≡ x)
      → apd (S¹-rec P x p) loop ≡ p

S¹-rec-nondep : ∀ {i} (A : Set i) (x : A) (p : x ≡ x) → (S¹ → A)
S¹-rec-nondep A x p #base = x

postulate  -- HIT
  S¹-β-loop-nondep : ∀ {i} (A : Set i) (x : A) (p : x ≡ x)
    → ap (S¹-rec-nondep A x p) loop ≡ p


-- S¹-rec-nondep : ∀ {i} (A : Set i) (x : A) (p : x ≡ x) → (S¹ → A)
-- S¹-rec-nondep A x p = S¹-rec (λ _ → A) x (trans-cst loop x ∘ p)

-- β-nondep : ∀ {i} (A : Set i) (x : A) (p : x ≡ x)
--   → ap (S¹-rec-nondep A x p) loop ≡ p
-- β-nondep A x p =
--   apd-trivial (S¹-rec-nondep A x p) loop ∘
--   (whisker-left (! (trans-cst loop _)) (β (λ _ → A) x (trans-cst loop _ ∘ p))
--   ∘ (! (concat-assoc (! (trans-cst loop _)) (trans-cst loop _) p)
--   ∘ whisker-right p (opposite-left-inverse (trans-cst loop _))))
