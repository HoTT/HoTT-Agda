{-# OPTIONS --without-K #-}

open import Base
import Homotopy.TruncationHIT as T

{-
The definition of the truncation is in TruncationHIT, here I just make some
arguments implicit, define easier to use helper functions and prove the
universal property
-}

module Homotopy.Truncation {i} where

τ : (n : ℕ) (A : Set i) → Set i
τ = T.τ

proj : {n : ℕ} {A : Set i} (x : A) → τ n A
proj {n} {A} = T.proj n A

abstract
  τ-is-hlevel : (n : ℕ) (A : Set i) → is-hlevel n (τ n A)
  τ-is-hlevel = T.τ-is-hlevel

τ-extend : ∀ {j} (n : ℕ) {A : Set i} {P : (τ n A) → Set j}
  ⦃ p : (x : τ n A) → is-hlevel n (P x) ⦄ (f : (x : A) → P (proj x))
  → ((x : τ n A) → P x)
τ-extend n {A} {P} ⦃ p ⦄ f = T.τ-rec _ _ _ f {transp} p where
  abstract
    transp : (pa : n ≡ 0) (x y : τ n A) (x* : P x) (y* : P y)
      → transport P (T.hack-prop n A pa x y) x* ≡ y*
    transp pa x y x* y* = π₁ (contr-is-prop
                               (transport (λ m → is-hlevel m _) pa (p y))
                              _ _)

τ-extend-nondep : ∀ {j} (n : ℕ) {A : Set i} {B : Set j}
  ⦃ p : is-hlevel n B ⦄ → ((f : A → B) → (τ n A → B))
τ-extend-nondep n {A} {B} ⦃ p ⦄ f = T.τ-rec-nondep _ _ _ f {transp} p where
  abstract
    transp : (pa : n ≡ 0) (x y : τ n A) (x* y* : B) → x* ≡ y*
    transp pa x y x* y* = π₁ (contr-is-prop
                               (transport (λ m → is-hlevel m _) pa p)
                              _ _)

-- Special syntax for hProp-reflection

[_] : (A : Set i) → Set i
[_] = τ 1

abstract
  []-is-prop : (A : Set i) → is-prop [ A ]
  []-is-prop = T.τ-is-hlevel 1

[]-extend : ∀ {j} {A : Set i} {P : [ A ] → Set j}
  ⦃ p : (x : [ A ]) → is-prop (P x) ⦄ (f : (x : A) → P (proj x))
  → ((x : [ A ]) → P x)
[]-extend f = τ-extend 1 f

[]-extend-nondep : ∀ {j} {A : Set i} {B : Set j} ⦃ p : is-prop B ⦄
  → ((f : A → B) → ([ A ] → B))
[]-extend-nondep f = τ-extend-nondep 1 f

-- Universal property of the truncation

abstract
  τ-up : ∀ {j} (n : ℕ) (A : Set i) (B : Set j)
    ⦃ p : is-hlevel n B ⦄
    → is-equiv (λ (f : τ n A → B) → (λ x → f (proj x)))
  τ-up n A B ⦃ p ⦄ = iso-is-eq _
    (τ-extend-nondep n)
    refl
    (λ f → funext (τ-extend n ⦃ p = λ x → ≡-is-hlevel n p ⦄
                            (λ x → refl _)))

  τ-extend-nondep-is-equiv : ∀ {j} (n : ℕ) (A : Set i) (B : Set j)
    ⦃ p : is-hlevel n B ⦄ → is-equiv (τ-extend-nondep n {A} {B})
  τ-extend-nondep-is-equiv n A B ⦃ p ⦄ = iso-is-eq _
    (λ f → f ◯ proj)
    (λ f → funext (τ-extend n ⦃ λ x → ≡-is-hlevel n p ⦄
                                (λ x → refl _)))
    refl

-- Equivalence associated to the universal property
τ-equiv : ∀ {j} (n : ℕ) (A : Set i) (B : Set j)
  ⦃ p : is-hlevel n B ⦄ → (τ n A → B) ≃ (A → B)
τ-equiv n A B = (_ , τ-up n _ _)

-- Equivalence associated to the universal property
τ-extend-equiv : ∀ {j} (n : ℕ) (A : Set i) (B : Set j)
  ⦃ p : is-hlevel n B ⦄ → (A → B) ≃ (τ n A → B)
τ-extend-equiv n A B = (τ-extend-nondep n , τ-extend-nondep-is-equiv n A B)

-- open import Homotopy.ReflectiveSubCategory

-- Reflective subcategory associated to the truncation
-- τ-rsc : (n : ℕ) → rsc {i}
-- τ-rsc n =
--   Rsc (is-hlevel n) (is-hlevel-is-prop n) (τ n) (λ A → proj {n} {A})
--       (τ-is-hlevel n) (τ-up n)
