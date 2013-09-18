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

  equiv-eq : ∀ {i j} {A : Set i} {B : Set j} {f g : A ≃ B} → π₁ f ≡ π₁ g → f ≡ g
  equiv-eq p = Σ-eq p $ prop-has-all-paths (is-equiv-is-prop _) _ _
