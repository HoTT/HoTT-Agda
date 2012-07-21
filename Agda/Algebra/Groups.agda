{-# OPTIONS --without-K #-}

open import Base
open import Truncation.Truncation
open import Truncation.TruncationUP
open import Integers.Integers

-- Formalization of 0-truncated groups
module Algebra.Groups where

record Pregroup i : Set (suc i) where
  constructor pregroup
  field
    -- Stuff
    ∣_∣ : Set i

    -- Structure
    _∙_ : ∣_∣ → ∣_∣ → ∣_∣
    e : ∣_∣
    _′ : ∣_∣ → ∣_∣  -- \'

    -- Properties
    assoc : (x y z : ∣_∣) → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
    right-unit : (x : ∣_∣) → x ∙ e ≡ x
    left-unit : (x : ∣_∣) → e ∙ x ≡ x
    right-inverse : (x : ∣_∣) → x ∙ (x ′) ≡ e
    left-inverse : (x : ∣_∣) → (x ′) ∙ x ≡ e
open Pregroup

record Group i : Set (suc i) where
  constructor group
  field
    g : Pregroup i
    set : is-set (∣ g ∣)
open Group

-- group-morphism : ∀ {i j} (A : Group i) (B : Group j) (f : ∣ A ∣ → ∣ B ∣) → Set (max i j)
-- group-morphism A B f = (x y : ∣ A ∣) → f (_∙_ A x y) ≡ _∙_ B (f x) (f y)

-- Group structure on [unit]
unit-group : ∀ {i} → Group i
unit-group {i} = group (pregroup unit (λ _ _ → tt) tt (λ _ → tt) (λ _ _ _ → refl tt) (λ _ → refl tt) (λ _ → refl tt) (λ _ → refl tt) (λ _ → refl tt)) unit-is-set

τ-pregroup : ∀ {i} → Pregroup i → Group i
τ-pregroup (pregroup ∣_∣ _∙_ e _′ assoc right-unit left-unit right-inverse left-inverse) = group (pregroup
  (τ 2 ∣_∣)
  (τ-extend-nondep 2 ⦃ p = →-hlevel 2 (τ-hlevel 2 _) ⦄ (λ x → τ-extend-nondep 2 ⦃ p = τ-hlevel 2 _ ⦄ (λ y → proj 2 _ (x ∙ y))))
  (proj 2 _ e)
  (τ-extend-nondep 2 {{p = τ-hlevel 2 _}} (λ x → proj 2 _ (x ′)))
  (τ-extend 2 ⦃ p = λ x → {!!} ⦄ {!!})
  {!!}
  {!!}
  {!!}
  {!!}) {!!}
