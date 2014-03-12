{-# OPTIONS --without-K #-}

open import Base

{-
    This file contains the lemma that
    a point (1 -> A) has n-connected fibers
    if A is (S n)-connected.

    The other direction will be added whenever
    it is needed.
-}

module Homotopy.PointConnected {i} (A : Set i) (a : A) where

  open import Homotopy.Connected
  open import Homotopy.Truncation
  open import Homotopy.PathTruncation

  point : unit {i} → A
  point _ = a

  abstract
    point-has-connected-fibers : ∀ {n} →
      is-connected (S n) A → has-connected-fibers n point
    point-has-connected-fibers {n} A-is-conn a₂ = center [a≡a₂]n , path
      where
        [a≡a₂]n : τ n (a ≡ a₂)
        [a≡a₂]n = connected-has-all-τ-paths A-is-conn a a₂

        center : τ n (a ≡ a₂) → τ n (hfiber point a₂)
        center = τ-extend-nondep ⦃ τ-is-truncated n _ ⦄
          (λ shift → proj $ tt , shift)

        path′ : ∀ f → proj f ≡ center [a≡a₂]n
        path′ (tt , a≡a₂) = ap center $ contr-has-all-paths
          (connected-has-connected-paths A-is-conn a a₂) (proj a≡a₂) [a≡a₂]n

        path : ∀ f → f ≡ center [a≡a₂]n
        path = τ-extend ⦃ λ _ → ≡-is-truncated n $ τ-is-truncated n _ ⦄ path′
