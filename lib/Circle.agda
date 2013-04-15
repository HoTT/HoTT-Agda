{-# OPTIONS --without-K #-}

open import lib.Base

module lib.Circle where

{-
Idea :

data S¹ : Type₀ where
  base : S¹
  loop : base ≡ base

I’m using Dan Licata’s trick to have a higher inductive type with definitional
reduction rule for [base]
-}

private
  data #S¹ : Type₀ where
    #base : #S¹

S¹ : Type₀
S¹ = #S¹

base : S¹
base = #base

postulate  -- HIT
  loop : base == base

S¹-elim : ∀ {i} {A : S¹ → Type i} (base* : A base)
  (loop* : base* == base* [ A ↓ loop ])
  → Π S¹ A
S¹-elim base* loop* #base = base*

postulate  -- HIT
  loop-β : ∀ {i} {A : S¹ → Type i} (base* : A base)
    (loop* : base* == base* [ A ↓ loop ])
    → apd (S¹-elim base* loop*) loop == loop*

S¹-rec : ∀ {i} {A : Type i} (base* : A) (loop* : base* == base*) → (S¹ → A)
S¹-rec base* loop* #base = base*

postulate  -- HIT
  loop-β' : ∀ {i} {A : Type i} (base* : A) (loop* : base* == base*)
    → ap (S¹-rec base* loop*) loop == loop*


-- S¹-rec-nondep : ∀ {i} (A : Type i) (x : A) (p : x ≡ x) → (S¹ → A)
-- S¹-rec-nondep A x p = S¹-rec (λ _ → A) x (trans-cst loop x ∘ p)

-- β-nondep : ∀ {i} (A : Type i) (x : A) (p : x ≡ x)
--   → ap (S¹-rec-nondep A x p) loop ≡ p
-- β-nondep A x p =
--   apd-trivial (S¹-rec-nondep A x p) loop ∘
--   (whisker-left (! (trans-cst loop _)) (β (λ _ → A) x (trans-cst loop _ ∘ p))
--   ∘ (! (concat-assoc (! (trans-cst loop _)) (trans-cst loop _) p)
--   ∘ whisker-right p (opposite-left-inverse (trans-cst loop _))))
