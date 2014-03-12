{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Truncation
open import Integers

-- Formalization of 0-truncated groups
module Algebra.Groups where

-- A pregroup is a group whose carrier is not a required to be a set (but
-- without higher coherences)

record pregroup i : Set (suc i) where
  -- constructor pregroup
  field
    -- Stuff
    carrier : Set i  -- \|

    -- Structure
    _∙_ : carrier → carrier → carrier  -- \.
    e : carrier
    _′ : carrier → carrier  -- \'

    -- Properties
    assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
    right-unit : ∀ x → x ∙ e ≡ x
    left-unit : ∀ x → e ∙ x ≡ x
    right-inverse : ∀ x → x ∙ (x ′) ≡ e
    left-inverse : ∀ x → (x ′) ∙ x ≡ e

record group i : Set (suc i) where
  -- constructor group
  field
    pre : pregroup i
  open pregroup pre
  field
    set : is-set carrier
  open pregroup pre public

-- Group structure on [unit]
unit-group : ∀ {i} → group i
unit-group {i} = record
  { pre = record
    { carrier = unit
    ; _∙_ = λ _ _ → tt
    ; e = tt
    ; _′ = λ _ → tt
    ; assoc = λ _ _ _ → refl
    ; right-unit = λ _ → refl
    ; left-unit = λ _ → refl
    ; right-inverse = λ _ → refl
    ; left-inverse = λ _ → refl
    }
  ; set = unit-is-set
  }

postulate  -- Tedious because I have a terrible definition of groups
  unit-group-unique : ∀ {i} (G : group i) →
    let open group G in (c : is-contr carrier) → G ≡ unit-group

-- Every pregroup can be truncated to a group
π₀-pregroup : ∀ {i} → pregroup i → group i
π₀-pregroup pre = record
  { pre = record
    { carrier = carrier₀
    ; _∙_ = _•₀_
    ; e = e₀
    ; _′ = _′₀
    ; assoc = assoc₀
    ; right-unit = right-unit₀
    ; left-unit = left-unit₀
    ; right-inverse = right-inverse₀
    ; left-inverse = left-inverse₀
    }
  ; set = carrier₀-is-set
  } where

    open pregroup pre

    carrier₀ : Set _
    carrier₀ = π₀ carrier

    carrier₀-is-set : is-set carrier₀
    carrier₀-is-set = π₀-is-set carrier

    _•₀_ : carrier₀ → carrier₀ → carrier₀
    _•₀_ = π₀-extend-nondep ⦃ →-is-set $ carrier₀-is-set ⦄
              (λ x → π₀-extend-nondep ⦃ carrier₀-is-set ⦄
                (λ y → proj (x ∙ y)))

    e₀ : π₀ carrier
    e₀ = proj e

    _′₀ : carrier₀ → carrier₀
    _′₀ = π₀-extend-nondep ⦃ carrier₀-is-set ⦄ (λ x → proj (x ′))

    abstract
      assoc₀ : ∀ x y z → (x •₀ y) •₀ z ≡ x •₀ (y •₀ z)
      assoc₀ =
        (π₀-extend ⦃ λ _ → Π-is-set λ _ → Π-is-set λ _ → ≡-is-set carrier₀-is-set ⦄
          (λ x → π₀-extend ⦃ λ _ → Π-is-set λ _ → ≡-is-set carrier₀-is-set ⦄
            (λ y → π₀-extend ⦃ λ _ → ≡-is-set carrier₀-is-set ⦄
              (λ z → ap proj (assoc x y z)))))

    abstract
      right-unit₀ : ∀ x → x •₀ e₀ ≡ x
      right-unit₀ =
        (π₀-extend ⦃ λ _ → ≡-is-set carrier₀-is-set ⦄
          (ap proj ◯ right-unit))

    abstract
      left-unit₀ : ∀ x → e₀ •₀ x ≡ x
      left-unit₀ =
        (π₀-extend ⦃ λ _ → ≡-is-set carrier₀-is-set ⦄
          (ap proj ◯ left-unit))

    abstract
      right-inverse₀ : ∀ x → x •₀ (x ′₀) ≡ e₀
      right-inverse₀ =
        (π₀-extend ⦃ λ _ → ≡-is-set carrier₀-is-set ⦄
          (ap proj ◯ right-inverse))

    abstract
      left-inverse₀ : ∀ x → (x ′₀) •₀ x ≡ e₀
      left-inverse₀ =
        (π₀-extend ⦃ λ _ → ≡-is-set carrier₀-is-set ⦄
          (ap proj ◯ left-inverse))

-- Not used

-- is-group-morphism : ∀ {i j} (A : Group i) (B : Group j)
-- (f : ∣ g A ∣ → ∣ g B ∣)
--   → Set (max i j)
-- is-group-morphism A B f =
--   (x y : ∣ g A ∣) → f (_∙_ (g A) x y) ≡ _∙_ (g B) (f x) (f y)

-- _≈_ : ∀ {i j} (A : Group i) (B : Group j) → Set (max i j)
-- A ≈ B = Σ (∣ g A ∣ → ∣ g B ∣) (λ f → is-equiv f × is-group-morphism A B f)
