{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.PushoutDef

-- Suspension is defined as a particular case of pushout

module Spaces.Suspension {i} (A : Set i) where

suspension-diag : pushout-diag i
suspension-diag = diag unit , unit , A , (λ _ → tt) , (λ _ → tt)

suspension : Set i
suspension = pushout suspension-diag

north : suspension
north = left tt

south : suspension
south = right tt

paths : A → north ≡ south
paths x = glue x

suspension-rec : ∀ {j} (P : suspension → Set j) (n : P north) (s : P south)
  (p : (x : A) → transport P (paths x) n ≡ s) → ((x : suspension) → P x)
suspension-rec P n s p = pushout-rec P (λ _ → n) (λ _ → s) p

suspension-β-paths : ∀ {j} (P : suspension → Set j) (n : P north) (s : P south)
  (p : (x : A) → transport P (paths x) n ≡ s)
  → ((x : A) → apd (suspension-rec P n s p) (paths x) ≡ p x)
suspension-β-paths P n s p =
  pushout-β-glue P (λ _ → n) (λ _ → s) p

suspension-rec-nondep : ∀ {j} (C : Set j) (n s : C) (p : A → n ≡ s)
  → (suspension → C)
suspension-rec-nondep C n s p =
  pushout-rec-nondep C (λ _ → n) (λ _ → s) p

suspension-β-paths-nondep : ∀ {j} (C : Set j) (n s : C) (p : A → n ≡ s)
  → ((x : A) → ap (suspension-rec-nondep C n s p) (paths x) ≡ p x)
suspension-β-paths-nondep C n s p =
  pushout-β-glue-nondep C (λ _ → n) (λ _ → s) p
