{-# OPTIONS --without-K #-}

open import Base
import Homotopy.TruncationHIT as T

{-
The definition of the truncation is in TruncationHIT, here I just make some
arguments implicit, define easier to use helper functions and prove the
universal property
-}

module Homotopy.Truncation {i} where

-- H-level numbering

hτ : (n : ℕ) (A : Set i) → Set i
hτ = T.τ

proj : {n : ℕ} {A : Set i} → (A → hτ n A)
proj {n} {A} = T.proj n A

hτ-is-hlevel : (n : ℕ) (A : Set i) → is-hlevel n (hτ n A)
hτ-is-hlevel = T.τ-is-hlevel

hτ-is-hlevel#instance : {n : ℕ} {A : Set i} → is-hlevel n (hτ n A)
hτ-is-hlevel#instance = T.τ-is-hlevel _ _

hτ-extend : ∀ {j} (n : ℕ) {A : Set i} {P : (hτ n A) → Set j}
  ⦃ p : (x : hτ n A) → is-hlevel n (P x) ⦄ (f : (x : A) → P (proj x))
  → ((x : hτ n A) → P x)
hτ-extend n {A} {P} ⦃ p ⦄ f = T.τ-rec _ _ _ f {transp} p where
  abstract
    transp : (pa : n ≡ 0) (x y : hτ n A) (x* : P x) (y* : P y)
      → transport P (T.hack-prop n A pa x y) x* ≡ y*
    transp pa x y x* y* = π₁ (contr-is-prop
                               (transport (λ m → is-hlevel m _) pa (p y))
                              _ _)

hτ-extend-nondep : ∀ {j} (n : ℕ) {A : Set i} {B : Set j}
  ⦃ p : is-hlevel n B ⦄ → ((f : A → B) → (hτ n A → B))
hτ-extend-nondep n {A} {B} ⦃ p ⦄ f = T.τ-rec-nondep _ _ _ f {transp} p where
  abstract
    transp : (pa : n ≡ 0) (x y : hτ n A) (x* y* : B) → x* ≡ y*
    transp pa x y x* y* = π₁ (contr-is-prop
                               (transport (λ m → is-hlevel m _) pa p)
                              _ _)

-- Homotopy theoretic numbering (for h-sets and above)

-- τ : (n : ℕ) (A : Set i) → Set i
-- τ n A = hτ (S (S n)) A

-- τ-extend : ∀ {j} (n : ℕ) {A : Set i} {P : (τ n A) → Set j}
--   ⦃ p : (x : τ n A) → is-hlevel (S (S n)) (P x) ⦄ (f : (x : A) → P (proj x))
--   → ((x : τ n A) → P x)
-- τ-extend n f = hτ-extend (S (S n)) f

-- τ-extend-nondep : ∀ {j} (n : ℕ) {A : Set i} {B : Set j}
--   ⦃ p : is-hlevel (S (S n)) B ⦄ → ((f : A → B) → (τ n A → B))
-- τ-extend-nondep n f = hτ-extend-nondep (S (S n)) f

-- is-truncated : (n : ℕ) → (Set i → Set i)
-- is-truncated n A = is-hlevel (S (S n)) A

-- τ-is-truncated : (n : ℕ) (A : Set i) → (is-truncated n (τ n A))
-- τ-is-truncated n A = hτ-is-hlevel (S (S n)) A

-- Special syntax for hProp-reflection

[_] : Set i → Set i
[_] = hτ 1

abstract
  []-is-prop : {A : Set i} → is-prop [ A ]
  []-is-prop = T.τ-is-hlevel 1 _

[]-extend : ∀ {j} {A : Set i} {P : [ A ] → Set j}
  ⦃ p : (x : [ A ]) → is-prop (P x) ⦄ (f : (x : A) → P (proj x))
  → ((x : [ A ]) → P x)
[]-extend f = hτ-extend 1 f

[]-extend-nondep : ∀ {j} {A : Set i} {B : Set j} ⦃ p : is-prop B ⦄
  → ((f : A → B) → ([ A ] → B))
[]-extend-nondep f = hτ-extend-nondep 1 f

-- Special syntax for hSet-reflection

π₀ : Set i → Set i
π₀ = hτ 2

abstract
  π₀-is-set : (A : Set i) → is-set (π₀ A)
  π₀-is-set A = T.τ-is-hlevel 2 _

π₀-extend : ∀ {j} {A : Set i} {P : π₀ A → Set j}
  ⦃ p : (x : π₀ A) → is-set (P x) ⦄ (f : (x : A) → P (proj x))
  → ((x : π₀ A) → P x)
π₀-extend f = hτ-extend 2 f

π₀-extend-nondep : ∀ {j} {A : Set i} {B : Set j} ⦃ p : is-set B ⦄
  → ((f : A → B) → (π₀ A → B))
π₀-extend-nondep f = hτ-extend-nondep 2 f

-- Universal property of the truncation

abstract
  hτ-up : ∀ {j} (n : ℕ) (A : Set i) (B : Set j)
    ⦃ p : is-hlevel n B ⦄
    → is-equiv (λ (f : hτ n A → B) → (λ x → f (proj x)))
  hτ-up n A B ⦃ p ⦄ = iso-is-eq _
    (hτ-extend-nondep n)
    refl
    (λ f → funext (hτ-extend n ⦃ p = λ x → ≡-is-hlevel n p ⦄
                             (λ x → refl _)))

  hτ-extend-nondep-is-equiv : ∀ {j} (n : ℕ) (A : Set i) (B : Set j)
    ⦃ p : is-hlevel n B ⦄ → is-equiv (hτ-extend-nondep n {A} {B})
  hτ-extend-nondep-is-equiv n A B ⦃ p ⦄ = iso-is-eq _
    (λ f → f ◯ proj)
    (λ f → funext (hτ-extend n ⦃ λ x → ≡-is-hlevel n p ⦄
                                (λ x → refl _)))
    refl

-- Equivalence associated to the universal property
hτ-equiv : ∀ {j} (n : ℕ) (A : Set i) (B : Set j)
  ⦃ p : is-hlevel n B ⦄ → (hτ n A → B) ≃ (A → B)
hτ-equiv n A B = (_ , hτ-up n _ _)

-- Equivalence associated to the universal property
hτ-extend-equiv : ∀ {j} (n : ℕ) (A : Set i) (B : Set j)
  ⦃ p : is-hlevel n B ⦄ → (A → B) ≃ (hτ n A → B)
hτ-extend-equiv n A B = (hτ-extend-nondep n , hτ-extend-nondep-is-equiv n A B)

-- open import Homotopy.ReflectiveSubCategory

-- Reflective subcategory associated to the truncation
-- τ-rsc : (n : ℕ) → rsc {i}
-- τ-rsc n =
--   Rsc (is-hlevel n) (is-hlevel-is-prop n) (τ n) (λ A → proj {n} {A})
--       (τ-is-hlevel n) (τ-up n)