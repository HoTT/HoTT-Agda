{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.Equivalences
open import lib.Univalence
open import lib.PathFunctor
open import lib.PathOver

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


module _ {i} {A : Type i} (f : A ≃ A) where

  P = S¹-rec A (ua f)

  loop-path : (a : A) → coe (ap P loop) a == f ☆ a
  loop-path a =
    coe (ap P loop) a =⟨ loop-β' A (ua f) |in-ctx (λ u → coe u a) ⟩
    coe (ua f) a      =⟨ coe-β (fst f) _ a ⟩
    f ☆ a ∎

  !loop-path : (a : A) → coe (ap P (! loop)) a == inverse f a
  !loop-path a =
    coe (ap P (! loop)) a
        =⟨ ap-! P loop |in-ctx (λ u → coe u a) ⟩
    coe (! (ap P loop)) a
        =⟨ loop-β' A (ua f) |in-ctx (λ u → coe (! u) a) ⟩
    coe (! (ua f)) a =⟨ coe-!β (fst f) _ a ⟩
    inverse f a ∎

  ↓-loop-out : {a a' : A} → a == a' [ P ↓ loop ] → f ☆ a == a'
  ↓-loop-out {a} {a'} p =
    f ☆ a =⟨ ! (loop-path a) ⟩
    coe (ap P loop) a =⟨ to-transp-out p ⟩
    a' ∎

{- -}

-- S¹-rec-nondep : ∀ {i} (A : Type i) (x : A) (p : x ≡ x) → (S¹ → A)
-- S¹-rec-nondep A x p = S¹-rec (λ _ → A) x (trans-cst loop x ∘ p)

-- β-nondep : ∀ {i} (A : Type i) (x : A) (p : x ≡ x)
--   → ap (S¹-rec-nondep A x p) loop ≡ p
-- β-nondep A x p =
--   apd-trivial (S¹-rec-nondep A x p) loop ∘
--   (whisker-left (! (trans-cst loop _)) (β (λ _ → A) x (trans-cst loop _ ∘ p))
--   ∘ (! (concat-assoc (! (trans-cst loop _)) (trans-cst loop _) p)
--   ∘ whisker-right p (opposite-left-inverse (trans-cst loop _))))
