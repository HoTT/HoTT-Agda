{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Truncation
open import Integers

-- Formalization of 0-truncated groups
module Algebra.Groups where

-- A pregroup is a group whose carrier is not a required to be a set (but
-- without higher coherences)

record Pregroup i : Set (suc i) where
  constructor pregroup
  field
    -- Stuff
    ∣_∣ : Set i  -- \|

    -- Structure
    _∙_ : ∣_∣ → ∣_∣ → ∣_∣  -- \.
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
unit-group {i} =
  group
    (pregroup
    unit
    (λ _ _ → tt)
    tt
    (λ _ → tt)
    (λ _ _ _ → refl tt)
    (λ _ → refl tt)
    (λ _ → refl tt)
    (λ _ → refl tt)
    (λ _ → refl tt))
  unit-is-set

postulate  -- Tedious because I have a terrible definition of groups
 unit-group-unique : ∀ {i} (G : Group i) (c : is-contr ∣ g G ∣) → G ≡ unit-group

-- Every pregroup can be truncated to a group
π₀-pregroup : ∀ {i} → Pregroup i → Group i
π₀-pregroup (pregroup ∣_∣ _∙_ e _′ assoc right-unit left-unit
             right-inverse left-inverse) =
  group (pregroup
    π₀-∣∣
    _π₀-•_
    π₀-e
    π₀-′
    π₀-assoc
    π₀-right-unit
    π₀-left-unit
    π₀-right-inverse
    π₀-left-inverse)
  (π₀-is-set _) where

    π₀→π₀-is-set : is-set (π₀ ∣_∣ → π₀ ∣_∣)
    π₀→π₀-is-set = →-is-hlevel 2 (π₀-is-set ∣_∣)
  
    π₀-∣∣ : Set _
    π₀-∣∣ = π₀ ∣_∣

    _π₀-•_ : π₀-∣∣ → π₀-∣∣ → π₀-∣∣
    _π₀-•_ = π₀-extend-nondep ⦃ →-is-hlevel 2 (π₀-is-set ∣_∣) ⦄
              (λ x → π₀-extend-nondep
                (λ y → proj (x ∙ y)))

    π₀-e : π₀-∣∣
    π₀-e = proj e

    π₀-′ : π₀-∣∣ → π₀-∣∣
    π₀-′ = π₀-extend-nondep (λ x → proj (x ′))

    abstract
      π₀-assoc : (x y z : π₀-∣∣) → (x π₀-• y) π₀-• z ≡ x π₀-• (y π₀-• z)
      π₀-assoc = 
        (π₀-extend ⦃ λ _ → Π-is-hlevel 2
                     (λ _ → Π-is-hlevel 2
                     (λ _ → hlevel-is-hlevel-S 2
                            (π₀-is-set _) _ _)) ⦄
          (λ x → π₀-extend ⦃ λ _ → Π-is-hlevel 2
                             (λ _ → hlevel-is-hlevel-S 2
                                    (π₀-is-set _) _ _) ⦄
            (λ y → π₀-extend ⦃ λ _ → hlevel-is-hlevel-S 2
                                      (π₀-is-set _) _ _ ⦄
              (λ z → map proj (assoc x y z)))))

    abstract
      π₀-right-unit : (x : π₀-∣∣) → x π₀-• π₀-e ≡ x
      π₀-right-unit =
        (π₀-extend ⦃ λ _ → hlevel-is-hlevel-S 2 (π₀-is-set _) _ _ ⦄
          (λ x → map proj (right-unit x)))

    abstract
      π₀-left-unit : (x : π₀-∣∣) → π₀-e π₀-• x ≡ x
      π₀-left-unit =
        (π₀-extend ⦃ λ _ → hlevel-is-hlevel-S 2 (π₀-is-set _) _ _ ⦄
          (λ x → map proj (left-unit x)))

    abstract
      π₀-right-inverse : (x : π₀-∣∣) → x π₀-• (π₀-′ x) ≡ π₀-e
      π₀-right-inverse =
        (π₀-extend ⦃ λ _ → hlevel-is-hlevel-S 2 (π₀-is-set _) _ _ ⦄
          (λ x → map proj (right-inverse x)))

    abstract
      π₀-left-inverse : (x : π₀-∣∣) → (π₀-′ x) π₀-• x ≡ π₀-e
      π₀-left-inverse =
        (π₀-extend ⦃ λ _ → hlevel-is-hlevel-S 2 (π₀-is-set _) _ _ ⦄
          (λ x → map proj (left-inverse x)))

-- Not used

-- is-group-morphism : ∀ {i j} (A : Group i) (B : Group j) (f : ∣ g A ∣ → ∣ g B ∣)
--   → Set (max i j)
-- is-group-morphism A B f =
--   (x y : ∣ g A ∣) → f (_∙_ (g A) x y) ≡ _∙_ (g B) (f x) (f y)

-- _≈_ : ∀ {i j} (A : Group i) (B : Group j) → Set (max i j)
-- A ≈ B = Σ (∣ g A ∣ → ∣ g B ∣) (λ f → is-equiv f × is-group-morphism A B f)
