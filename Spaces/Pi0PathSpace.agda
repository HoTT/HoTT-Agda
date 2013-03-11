{-# OPTIONS --without-K #-}

{-
  Specialized constructs and lemmas for π₀ (x ≡ y)

  Should be rewritten with Algebra.Group.
-}

open import Base

module Spaces.Pi0PathSpace where

open import HLevel
open import HLevelBis
open import Homotopy.Truncation
open import Homotopy.PathTruncation

_≡₀_ : ∀ {i} {A : Set i} → A → A → Set i
_≡₀_ x y = π₀ (x ≡ y)

private
  eq : ∀ {i} {A : Set i} {x y : A} → (x ≡₀ y) ≃ (proj {n = ⟨1⟩} x ≡ proj y)
  eq = τ-path-equiv-path-τ-S

infix 8 _∘₀_  -- \o\0
_∘₀_ : ∀ {i} {A : Set i} {x y z : A} → x ≡₀ y → y ≡₀ z → x ≡₀ z
p ∘₀ q = inverse eq $ eq ☆ p ∘ eq ☆ q

!₀ : ∀ {i} {A : Set i} {x y : A} → x ≡₀ y → y ≡₀ x
!₀ = τ-ap !

refl₀ : ∀ {i} {A : Set i} (x : A) → x ≡₀ x
refl₀ x = proj $ refl x

ap₀ : ∀ {i} {A B : Set i} {x y : A} (f : A → B)
  → x ≡₀ y → f x ≡₀ f y
ap₀ f = τ-ap $ ap f

refl₀-right-unit : ∀ {i} {A : Set i} {x y : A} (q : x ≡₀ y) → (q ∘₀ refl₀ y) ≡ q
refl₀-right-unit {x = x} {y} = π₀-extend
  ⦃ λ _ →  ≡-is-set $ π₀-is-set (x ≡ y) ⦄
  $ lemma x y
  where
    lemma : ∀ x y (q : x ≡ y) → (proj q ∘₀ refl₀ _) ≡ proj q
    lemma ._ ._ (refl _) = inverse-left-inverse eq _
