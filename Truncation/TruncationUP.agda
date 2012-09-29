{-# OPTIONS --without-K #-}

open import Base
open import Truncation.Truncation

module Truncation.TruncationUP where

-- We can extend a function to the truncation, if the codomain is of the correct
-- hlevel (renamings of [τ-rec] and [τ-rec-nondep])
τ-extend : ∀ {i j} (n : ℕ) ⦃ >0 : n ≢ 0 ⦄ {A : Set i} {P : (τ n A) → Set j}
  ⦃ p : (x : τ n A) → is-hlevel n (P x) ⦄ (f : (x : A) → P (proj _ _ x))
  → ((x : τ n A) → P x)
τ-extend n ⦃ p = p ⦄ f = τ-rec _ _ _ f p

τ-extend-nondep : ∀ {i j} (n : ℕ) ⦃ >0 : n ≢ 0 ⦄ {A : Set i} {B : Set j}
  ⦃ p : is-hlevel n B ⦄ → ((f : A → B) → (τ n A → B))
τ-extend-nondep n ⦃ p = p ⦄ f = τ-rec-nondep _ _ _ f p

-- Universal property of the truncation
abstract
  τ-up : ∀ {i j} (n : ℕ) ⦃ >0 : n ≢ 0 ⦄ (A : Set i) (B : Set j)
    ⦃ p : is-hlevel n B ⦄
    → is-equiv (λ (f : τ n A → B) → (λ x → f (proj n A x)))
  τ-up n A B ⦃ p ⦄ = iso-is-eq _
    (τ-extend-nondep n)
    refl
    (λ f → funext-dep (τ-extend n ⦃ p = λ x → paths-hlevel-n n B p ⦄
                            (λ x → refl _)))

-- Equivalence associated to the universal property
τ-equiv : ∀ {i j} (n : ℕ) ⦃ >0 : n ≢ 0 ⦄ (A : Set i) (B : Set j)
  ⦃ p : is-hlevel n B ⦄ → (τ n A → B) ≃ (A → B)
τ-equiv n A B = (_ , τ-up n _ _)

open import CategoryTheory.ReflectiveSubCategory

-- Reflective subcategory associated to the truncation
τ-rsc : ∀ {i} (n : ℕ) ⦃ >0 : n ≢ 0 ⦄ → rsc {i}
τ-rsc n =
  Rsc (is-hlevel n) (is-hlevel-is-prop n) (τ n) (proj n) (τ-hlevel n) (τ-up n)
