{-# OPTIONS --without-K #-}

open import Base
import Homotopy.TruncationHIT as T

{-
The definition of the truncation is in TruncationHIT, here I just make some
arguments implicit, define easier to use helper functions and prove the
universal property
-}

module Homotopy.Truncation {i} where

τ : (n : ℕ₋₂) → (Set i → Set i)
τ = T.τ

proj : {n : ℕ₋₂} {A : Set i} → (A → τ n A)
proj {n} {A} = T.proj n A

τ-is-truncated : (n : ℕ₋₂) (A : Set i) → is-truncated n (τ n A)
τ-is-truncated = T.τ-is-truncated

τ-is-truncated#instance : {n : ℕ₋₂} {A : Set i} → is-truncated n (τ n A)
τ-is-truncated#instance = T.τ-is-truncated _ _

τ-extend : ∀ {j} {n : ℕ₋₂} {A : Set i} {P : (τ n A) → Set j}
  ⦃ p : (x : τ n A) → is-truncated n (P x) ⦄ (f : (x : A) → P (proj x))
  → ((x : τ n A) → P x)
τ-extend {j} {n} {A} {P} ⦃ p ⦄ f = T.τ-rec _ _ _ f {transp} p where
  abstract
    transp : (pa : n ≡ ⟨-2⟩) (x y : τ n A) (x* : P x) (y* : P y)
      → transport P (T.hack-prop n A pa x y) x* ≡ y*
    transp pa x y x* y* = π₁ (contr-is-prop
                               (transport (λ m → is-truncated m _) pa (p y))
                              _ _)

τ-extend-nondep : ∀ {j} {n : ℕ₋₂} {A : Set i} {B : Set j}
  ⦃ p : is-truncated n B ⦄ → ((f : A → B) → (τ n A → B))
τ-extend-nondep {j} {n} {A} {B} ⦃ p ⦄ f = T.τ-rec-nondep _ _ _ f {transp} p
  where
  abstract
    transp : (pa : n ≡ ⟨-2⟩) (x y : τ n A) (x* y* : B) → x* ≡ y*
    transp pa x y x* y* = π₁ (contr-is-prop
                               (transport (λ m → is-truncated m _) pa p)
                              _ _)

-- Special syntax for hProp-reflection

[_] : Set i → Set i
[_] = τ ⟨-1⟩

abstract
  []-is-prop : {A : Set i} → is-prop [ A ]
  []-is-prop = T.τ-is-truncated _ _

[]-extend : ∀ {j} {A : Set i} {P : [ A ] → Set j}
  ⦃ p : (x : [ A ]) → is-prop (P x) ⦄ (f : (x : A) → P (proj x))
  → ((x : [ A ]) → P x)
[]-extend f = τ-extend f

[]-extend-nondep : ∀ {j} {A : Set i} {B : Set j} ⦃ p : is-prop B ⦄
  → ((f : A → B) → ([ A ] → B))
[]-extend-nondep f = τ-extend-nondep f

-- Special syntax for hSet-reflection

π₀ : Set i → Set i
π₀ = τ ⟨0⟩

π₀-is-set : (A : Set i) → is-set (π₀ A)
π₀-is-set A = T.τ-is-truncated _ _

π₀-extend : ∀ {j} {A : Set i} {P : π₀ A → Set j}
  ⦃ p : (x : π₀ A) → is-set (P x) ⦄ (f : (x : A) → P (proj x))
  → ((x : π₀ A) → P x)
π₀-extend f = τ-extend f

π₀-extend-nondep : ∀ {j} {A : Set i} {B : Set j} ⦃ p : is-set B ⦄
  → ((f : A → B) → (π₀ A → B))
π₀-extend-nondep f = τ-extend-nondep f

-- Universal property of the truncation

abstract
  τ-up : ∀ {j} (n : ℕ₋₂) (A : Set i) (B : Set j)
    ⦃ p : is-truncated n B ⦄
    → is-equiv (λ (f : τ n A → B) → (λ x → f (proj x)))
  τ-up n A B ⦃ p ⦄ = iso-is-eq _
    (τ-extend-nondep)
    (λ _ → refl)
    (λ f → funext (τ-extend ⦃ p = λ x → ≡-is-truncated n p ⦄
                             (λ x → refl)))

  τ-extend-nondep-is-equiv : ∀ {j} (n : ℕ₋₂) (A : Set i) (B : Set j)
    ⦃ p : is-truncated n B ⦄ → is-equiv (τ-extend-nondep {n = n} {A} {B})
  τ-extend-nondep-is-equiv n A B ⦃ p ⦄ = iso-is-eq _
    (λ f → f ◯ proj)
    (λ f → funext (τ-extend ⦃ λ x → ≡-is-truncated n p ⦄
                                (λ x → refl)))
    (λ _ → refl)

-- Equivalence associated to the universal property
τ-equiv : ∀ {j} (n : ℕ₋₂) (A : Set i) (B : Set j)
  ⦃ p : is-truncated n B ⦄ → (τ n A → B) ≃ (A → B)
τ-equiv n A B = (_ , τ-up n _ _)

-- Equivalence associated to the universal property
τ-extend-equiv : ∀ {j} (n : ℕ₋₂) (A : Set i) (B : Set j)
  ⦃ p : is-truncated n B ⦄ → (A → B) ≃ (τ n A → B)
τ-extend-equiv n A B = (τ-extend-nondep , τ-extend-nondep-is-equiv n A B)

τ-fmap : {n : ℕ₋₂} {A B : Set i} → ((A → B) → (τ n A → τ n B))
τ-fmap f = τ-extend-nondep (proj ◯ f)

τ-fpmap : {n : ℕ₋₂} {A B : Set i} {f g : A → B} (h : (a : A) → f a ≡ g a)
  → ((a : τ n A) → τ-fmap f a ≡ τ-fmap g a)
τ-fpmap h = τ-extend ⦃ λ _ → ≡-is-truncated _ (τ-is-truncated _ _) ⦄
              (ap proj ◯ h)
