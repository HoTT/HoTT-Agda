{-# OPTIONS --without-K #-}

open import Base
import Truncation.TruncationHIT as T

module Truncation.Truncation {i} where

τ : (n : ℕ) (A : Set i) → Set i
τ = T.τ

proj : (n : ℕ) (A : Set i) (x : A) → τ n A
proj = T.proj

abstract
  τ-hlevel : (n : ℕ) (A : Set i) → is-hlevel n (τ n A)
  τ-hlevel = T.τ-hlevel

τ-extend : ∀ {j} (n : ℕ) {A : Set i} {P : (τ n A) → Set j}
  ⦃ p : (x : τ n A) → is-hlevel n (P x) ⦄ (f : (x : A) → P (proj n A x))
  → ((x : τ n A) → P x)
τ-extend n {A} {P} ⦃ p ⦄ f = T.τ-rec _ _ _ f transp p where
  transp : (pa : n ≡ 0) (x y : τ n A) (x* : P x) (y* : P y)
    → transport P (T.hack-prop n A pa x y) x* ≡ y*
  transp pa x y x* y* = π₁ (contr-is-prop
                             (transport (λ m → is-hlevel m _) pa (p y))
                            _ _)

τ-extend-nondep : ∀ {j} (n : ℕ) {A : Set i} {B : Set j}
  ⦃ p : is-hlevel n B ⦄ → ((f : A → B) → (τ n A → B))
τ-extend-nondep n {A} {B} ⦃ p ⦄ f = T.τ-rec-nondep _ _ _ f transp p where
  transp : (pa : n ≡ 0) (x y : τ n A) (x* y* : B) → x* ≡ y*
  transp pa x y x* y* = π₁ (contr-is-prop
                             (transport (λ m → is-hlevel m _) pa p)
                            _ _)

-- Universal property of the truncation
abstract
  τ-up : ∀ {j} (n : ℕ) (A : Set i) (B : Set j)
    ⦃ p : is-hlevel n B ⦄
    → is-equiv (λ (f : τ n A → B) → (λ x → f (proj n A x)))
  τ-up n A B ⦃ p ⦄ = iso-is-eq _
    (τ-extend-nondep n)
    refl
    (λ f → funext-dep (τ-extend n ⦃ p = λ x → paths-hlevel-n n B p ⦄
                            (λ x → refl _)))

-- Equivalence associated to the universal property
τ-equiv : ∀ {j} (n : ℕ) (A : Set i) (B : Set j)
  ⦃ p : is-hlevel n B ⦄ → (τ n A → B) ≃ (A → B)
τ-equiv n A B = (_ , τ-up n _ _)

open import CategoryTheory.ReflectiveSubCategory

-- Reflective subcategory associated to the truncation
τ-rsc : (n : ℕ) → rsc {i}
τ-rsc n =
  Rsc (is-hlevel n) (is-hlevel-is-prop n) (τ n) (proj n) (τ-hlevel n) (τ-up n)
