{-# OPTIONS --without-K #-}

{-
  Specialized constructs and lemmas for π₀ (x ≡ y)

  Should be rewritten with something like Algebra.Groupoid.
-}

open import Base

module Spaces.Pi0PathSpace {i} where

open import HLevel
open import HLevelBis
open import Homotopy.Truncation
open import Homotopy.PathTruncation
open import Algebra.Applicative

open Applicative {i} {F = π₀} π₀-is-applicative

_≡₀_ : ∀ {A : Set i} → A → A → Set i
_≡₀_ x y = π₀ (x ≡ y)

infix 8 _∘₀_  -- \o\0
_∘₀_ : ∀ {A : Set i} {x y z : A} → x ≡₀ y → y ≡₀ z → x ≡₀ z
p ∘₀ q = pure _∘_ ✭ p ✭ q

!₀ : ∀ {A : Set i} {x y : A} → x ≡₀ y → y ≡₀ x
!₀ = τ-ap !

refl₀ : ∀ {A : Set i} (x : A) → x ≡₀ x
refl₀ x = proj $ refl x

ap₀ : ∀ {A B : Set i} {x y : A} (f : A → B)
  → x ≡₀ y → f x ≡₀ f y
ap₀ f = τ-ap $ ap f

refl₀-right-unit : ∀ {A : Set i} {x y : A} (q : x ≡₀ y) → (q ∘₀ refl₀ y) ≡ q
refl₀-right-unit {x = x} {y} = π₀-extend
  ⦃ λ _ →  ≡-is-set $ π₀-is-set (x ≡ y) ⦄
  (λ x → ap proj $ refl-right-unit x)
