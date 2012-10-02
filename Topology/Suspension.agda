{-# OPTIONS --without-K #-}

open import Base
open import CategoryTheory.PushoutDef

-- Suspension is defined as a particular case of pushout

module Topology.Suspension {i} (A : Set i) where

suspension-diag : pushout-diag i
suspension-diag = diag unit , unit , A , (λ _ → tt) , (λ _ → tt)

suspension : Set i
suspension = pushout suspension-diag

north : suspension
north = left suspension-diag tt

south : suspension
south = right suspension-diag tt

paths : A → north ≡ south
paths x = glue suspension-diag x

suspension-rec : ∀ {j} (P : suspension → Set j) (n : P north) (s : P south)
  (p : (x : A) → transport P (paths x) n ≡ s) → ((x : suspension) → P x)
suspension-rec P n s p = pushout-rec suspension-diag P (λ _ → n) (λ _ → s) p

suspension-β-paths : ∀ {j} (P : suspension → Set j) (n : P north) (s : P south)
  (p : (x : A) → transport P (paths x) n ≡ s)
  → ((x : A) → map-dep (suspension-rec P n s p) (paths x) ≡ p x)
suspension-β-paths P n s p =
  pushout-β-glue suspension-diag P (λ _ → n) (λ _ → s) p

suspension-rec-nondep : ∀ {j} (C : Set j) (n s : C) (p : A → n ≡ s)
  → (suspension → C)
suspension-rec-nondep C n s p =
  pushout-rec-nondep suspension-diag C (λ _ → n) (λ _ → s) p

suspension-β-paths-nondep : ∀ {j} (C : Set j) (n s : C) (p : A → n ≡ s)
  → ((x : A) → map (suspension-rec-nondep C n s p) (paths x) ≡ p x)
suspension-β-paths-nondep C n s p =
  pushout-β-glue-nondep suspension-diag C (λ _ → n) (λ _ → s) p
