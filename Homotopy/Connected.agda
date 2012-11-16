{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Truncation

module Homotopy.Connected {i} where

is-connected : ℕ₋₂ → Set i → Set i
is-connected n A = is-contr (τ n A)

is-connected-is-prop : (n : ℕ₋₂) {A : Set i} → is-prop (is-connected n A)
is-connected-is-prop n = is-contr-is-prop

module _ (n : ℕ₋₂) (A : Set i) where

  private
    τ-to-ττ : τ n A → τ n (τ (S n) A)
    τ-to-ττ = τ-extend-nondep (proj ◯ proj)

    τ-is-truncated-S : is-truncated (S n) (τ n A)
    τ-is-truncated-S = truncated-is-truncated-S n (τ-is-truncated n A)

    ττ-to-τ : τ n (τ (S n) A) → τ n A
    ττ-to-τ = τ-extend-nondep (τ-extend-nondep proj)

    τ-inv-ττ : (x : τ n A) → ττ-to-τ (τ-to-ττ x) ≡ x
    τ-inv-ττ = τ-extend ⦃ λ _ → ≡-is-truncated n (τ-is-truncated n A) ⦄
                 (λ _ → refl _)

    ττ-inv-τ : (x : τ n (τ (S n) A)) → τ-to-ττ (ττ-to-τ x) ≡ x
    ττ-inv-τ = τ-extend ⦃ λ _ → ≡-is-truncated n (τ-is-truncated n _) ⦄
                 (τ-extend ⦃ λ _ → truncated-is-truncated-S n
                                     (≡-is-truncated n
                                       (τ-is-truncated n _)) ⦄
                   (λ _ → refl _))

  τ-equiv-ττ : τ n A ≃ τ n (τ (S n) A)
  τ-equiv-ττ = (τ-to-ττ , iso-is-eq _ ττ-to-τ ττ-inv-τ τ-inv-ττ)

  ττ-equiv-τ : τ n (τ (S n) A) ≃ τ n A
  ττ-equiv-τ = (ττ-to-τ , iso-is-eq _ τ-to-ττ τ-inv-ττ ττ-inv-τ)

abstract
  contr-is-connected : (n : ℕ₋₂) {A : Set i}
    → (is-contr A → is-connected n A)
  contr-is-connected n (x , p) =
    (proj x , τ-extend ⦃ λ _ → ≡-is-truncated n (τ-is-truncated n _) ⦄
                (λ _ → map proj (contr-has-all-paths (x , p) _ _)))

  connected-S-is-connected : (n : ℕ₋₂) {A : Set i}
    → (is-connected (S n) A → is-connected n A)
  connected-S-is-connected n p =
    equiv-types-truncated _ (ττ-equiv-τ n _) (contr-is-connected n p)
