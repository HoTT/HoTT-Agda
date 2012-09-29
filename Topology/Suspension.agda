{-# OPTIONS --without-K #-}

open import Base
open import CategoryTheory.PushoutDef

-- Suspension is defined as a particular case of pushout

module Topology.Suspension {i} (A : Set i) where

suspension : Set i
suspension = pushout (unit {i}) (unit {i}) A (λ _ → tt) (λ _ → tt)

north : suspension
north = left _ _ _ _ _ tt

south : suspension
south = right _ _ _ _ _ tt

paths : A → north ≡ south
paths x = glue _ _ _ _ _ x

suspension-rec : ∀ {j} (P : suspension → Set j) (n : P north) (s : P south)
  (p : (x : A) → transport P (paths x) n ≡ s) → ((x : suspension) → P x)
suspension-rec P n s p = pushout-rec _ _ _ _ _ P (λ _ → n) (λ _ → s) p

suspension-β-paths : ∀ {j} (P : suspension → Set j) (n : P north) (s : P south)
  (p : (x : A) → transport P (paths x) n ≡ s)
  → ((x : A) → map-dep (suspension-rec P n s p) (paths x) ≡ p x)
suspension-β-paths P n s p = pushout-β-glue _ _ _ _ _ P (λ _ → n) (λ _ → s) p

suspension-rec-nondep : ∀ {j} (C : Set j) (n s : C) (p : A → n ≡ s)
  → (suspension → C)
suspension-rec-nondep C n s p =
  pushout-rec-nondep _ _ _ _ _ C (λ _ → n) (λ _ → s) p

suspension-β-paths-nondep : ∀ {j} (C : Set j) (n s : C) (p : A → n ≡ s)
  → ((x : A) → map (suspension-rec-nondep C n s p) (paths x) ≡ p x)
suspension-β-paths-nondep C n s p =
  pushout-β-glue-nondep _ _ _ _ _ C (λ _ → n) (λ _ → s) p
