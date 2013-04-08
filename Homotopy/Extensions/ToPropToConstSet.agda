{-# OPTIONS --without-K #-}

open import Base
open import HLevel

module Homotopy.Extensions.ToPropToConstSet {i}
  {A B : Set i} ⦃ B-is-set : is-set B ⦄
  (f : A → B) (f-is-const : ∀ a₁ a₂ → f a₁ ≡ f a₂) where

  open import Homotopy.Truncation
  open import Homotopy.Skeleton

  private
    skel : Set i
    skel = π₀ (skeleton₁ f)

    abstract
      skel-has-all-paths : has-all-paths skel
      skel-has-all-paths =
        π₀-extend ⦃ λ _ → Π-is-set λ _ → ≡-is-set $ π₀-is-set _ ⦄
          (skeleton₁-rec (λ s₁ → ∀ s₂ → proj s₁ ≡ s₂)
            (λ a₁ → π₀-extend ⦃ λ _ → ≡-is-set $ π₀-is-set _ ⦄
              (skeleton₁-rec (λ s₂ → proj (point a₁) ≡ proj s₂)
                (λ a₂ → ap proj $ link a₁ a₂ $ f-is-const a₁ a₂)
                (λ _ _ _ → prop-has-all-paths (π₀-is-set _ _ _) _ _)))
            (λ _ _ _ → funext λ _ → prop-has-all-paths (π₀-is-set _ _ _) _ _))

    skel-is-prop : is-prop skel
    skel-is-prop = all-paths-is-prop skel-has-all-paths

  cst-extend : [ A ] → B
  cst-extend = π₀-extend-nondep ⦃ B-is-set ⦄ skeleton₁-lifted
            ◯ []-extend-nondep ⦃ skel-is-prop ⦄ (proj ◯ point)
