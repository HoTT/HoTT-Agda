{-# OPTIONS --without-K #-}

{-
  This file lists some basic facts about equivalences
  that have to be put in a separate file due to dependency.
-}

open import Types
open import Functions
open import Paths
open import HLevel
open import Equivalences
open import Univalence
open import HLevelBis

module EquivalenceLemmas where

  equiv-eq : ∀ {i} {A B : Set i} {f g : A ≃ B} → π₁ f ≡ π₁ g → f ≡ g
  equiv-eq p = Σ-eq p $ prop-has-all-paths (is-equiv-is-prop _) _ _

  trans-app≃app : ∀ {i j} {A : Set i} (f g : A → Set j) {x y : A} (p : x ≡ y)
    (q : f x ≃ g x)
    → transport (λ x → f x ≃ g x) p q
    ≡ (path-to-eq $ ap f p) ⁻¹  ⊙ (q ⊙ path-to-eq (ap g p))
  trans-app≃app f g (refl _) q = equiv-eq $ refl _
