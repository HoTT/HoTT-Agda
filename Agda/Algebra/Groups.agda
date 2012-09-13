{-# OPTIONS --without-K #-}

open import Base
open import Truncation.Truncation
open import Truncation.TruncationUP
open import Integers.Integers

-- Formalization of 0-truncated groups
module Algebra.Groups where

-- A pregroup is a group whose carrier is not a set (but without higher coherences)

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

-- Group structure on [unit]
unit-group : ∀ {i} → Group i
unit-group {i} = group (pregroup unit (λ _ _ → tt) tt (λ _ → tt) (λ _ _ _ → refl tt) (λ _ → refl tt) (λ _ → refl tt) (λ _ → refl tt) (λ _ → refl tt)) unit-is-set

-- Every pregroup can be truncated to a group
abstract
  τ-pregroup : ∀ {i} → Pregroup i → Group i
  τ-pregroup (pregroup ∣_∣ _∙_ e _′ assoc right-unit left-unit right-inverse left-inverse) = group (pregroup
    (τ 2 ∣_∣)
    (τ-extend-nondep 2 ⦃ p = →-hlevel 2 (τ-hlevel 2 _) ⦄ (λ x → τ-extend-nondep 2 ⦃ p = τ-hlevel 2 _ ⦄ (λ y → proj 2 _ (x ∙ y))))
    (proj 2 _ e)
    (τ-extend-nondep 2 ⦃ p = τ-hlevel 2 _ ⦄ (λ x → proj 2 _ (x ′)))
    (τ-extend 2 ⦃ p = λ x → pi-hlevel 2 (λ _ → pi-hlevel 2 (λ _ → is-increasing-hlevel 2 (τ 2 ∣_∣) τ-is-set _ _)) ⦄
      (λ x → τ-extend 2 ⦃ p = λ _ → pi-hlevel 2 (λ _ → is-increasing-hlevel 2 (τ 2 ∣_∣) τ-is-set _ _) ⦄
        (λ y → τ-extend 2 ⦃ p = λ _ → is-increasing-hlevel 2 (τ 2 ∣_∣) τ-is-set _ _ ⦄
          (λ z → map (proj 2 _) (assoc x y z)))))
    (τ-extend 2 ⦃ p = λ _ → is-increasing-hlevel 2 (τ 2 ∣_∣) τ-is-set _ _ ⦄ (λ x → map (proj 2 _) (right-unit x)))
    (τ-extend 2 ⦃ p = λ _ → is-increasing-hlevel 2 (τ 2 ∣_∣) τ-is-set _ _ ⦄ (λ x → map (proj 2 _) (left-unit x)))
    (τ-extend 2 ⦃ p = λ _ → is-increasing-hlevel 2 (τ 2 ∣_∣) τ-is-set _ _ ⦄ (λ x → map (proj 2 _) (right-inverse x)))
    (τ-extend 2 ⦃ p = λ _ → is-increasing-hlevel 2 (τ 2 ∣_∣) τ-is-set _ _ ⦄ (λ x → map (proj 2 _) (left-inverse x)))
    ) τ-is-set
  
    where
    τ-is-set : is-set (τ 2 ∣_∣)
    τ-is-set = τ-hlevel 2 ∣_∣
  
    τ→τ-is-set : is-set (τ 2 ∣_∣ → τ 2 ∣_∣)
    τ→τ-is-set = →-hlevel 2 τ-is-set

is-group-morphism : ∀ {i j} (A : Group i) (B : Group j) (f : ∣ g A ∣ → ∣ g B ∣) → Set (max i j)
is-group-morphism A B f = (x y : ∣ g A ∣) → f (_∙_ (g A) x y) ≡ _∙_ (g B) (f x) (f y)

_≈_ : ∀ {i j} (A : Group i) (B : Group j) → Set (max i j)
A ≈ B = Σ (∣ g A ∣ → ∣ g B ∣) (λ f → is-equiv f × is-group-morphism A B f)

-- ≈-to-≡ : ∀ {i} (A B : Group i) (f : A ≈ B) → A ≡ B
-- ≈-to-≡ A B f = transport _ (eq-to-path (π₁ f , (π₁ (π₂ f)))) {!!}
