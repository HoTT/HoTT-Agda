{-# OPTIONS --without-K #-}

{-
  Specialized constructs and lemmas for π₀ (x ≡ y)

  Should be rewritten with something like Algebra.Groupoid.
-}

open import Base

module Spaces.Pi0Paths where

open import HLevel
open import HLevelBis
open import Homotopy.Truncation
open import Homotopy.PathTruncation

_≡₀_ : ∀ {i} {A : Set i} → A → A → Set i
_≡₀_ x y = π₀ (x ≡ y)

infix 8 _∘₀_  -- \o\0
_∘₀_ : ∀ {i} {A : Set i} {x y z : A} → x ≡₀ y → y ≡₀ z → x ≡₀ z
_∘₀_ =
  π₀-extend-nondep ⦃ →-is-set $ π₀-is-set _ ⦄ (λ p →
    π₀-extend-nondep ⦃ π₀-is-set _ ⦄ (λ q →
      proj $ p ∘ q))

!₀ : ∀ {i} {A : Set i} {x y : A} → x ≡₀ y → y ≡₀ x
!₀ = π₀-extend-nondep ⦃ π₀-is-set _ ⦄ (proj ◯ !)

refl₀ : ∀ {i} {A : Set i} (x : A) → x ≡₀ x
refl₀ x = proj $ refl x

ap₀ : ∀ {i j} {A : Set i} {B : Set j} {x y : A} (f : A → B)
  → x ≡₀ y → f x ≡₀ f y
ap₀ f = π₀-extend-nondep ⦃ π₀-is-set _ ⦄ (proj ◯ ap f)

module _ {i} {A : Set i} where

  refl₀-right-unit : ∀ {x y : A} (q : x ≡₀ y) → (q ∘₀ refl₀ y) ≡ q
  refl₀-right-unit {x = x} {y} = π₀-extend
    ⦃ λ _ →  ≡-is-set $ π₀-is-set (x ≡ y) ⦄
    (λ x → ap proj $ refl-right-unit x)

  refl₀-left-unit : ∀ {x y : A} (q : x ≡₀ y) → (refl₀ x ∘₀ q) ≡ q
  refl₀-left-unit {x = x} {y} = π₀-extend
    ⦃ λ _ →  ≡-is-set $ π₀-is-set (x ≡ y) ⦄
    (λ x → refl $ proj x)

  concat₀-assoc : {x y z t : A} (p : x ≡₀ y) (q : y ≡₀ z) (r : z ≡₀ t)
    → (p ∘₀ q) ∘₀ r ≡ p ∘₀ (q ∘₀ r)
  concat₀-assoc =
    π₀-extend ⦃ λ _ → Π-is-set λ _ → Π-is-set λ _ → ≡-is-set $ π₀-is-set _ ⦄ (λ p →
      π₀-extend ⦃ λ _ → Π-is-set λ _ → ≡-is-set $ π₀-is-set _ ⦄ (λ q →
        π₀-extend ⦃ λ _ → ≡-is-set $ π₀-is-set _ ⦄ (λ r →
          ap proj $ concat-assoc p q r)))

  concat₀-ap₀ : ∀ {j} {B : Set j} (f : A → B) {x y z : A} (p : x ≡₀ y) (q : y ≡₀ z)
    → ap₀ f p ∘₀ ap₀ f q ≡ ap₀ f (p ∘₀ q)
  concat₀-ap₀ f =
    π₀-extend ⦃ λ _ → Π-is-set λ _ → ≡-is-set $ π₀-is-set _ ⦄ (λ p →
      π₀-extend ⦃ λ _ → ≡-is-set $ π₀-is-set _ ⦄ (λ q →
        ap proj $ concat-ap f p q))

  trans-id≡₀cst : {a b c : A} (p : b ≡ c) (q : b ≡₀ a)
    → transport (λ x → x ≡₀ a) p q ≡ proj (! p) ∘₀ q
  trans-id≡₀cst (refl _) q = ! $ refl₀-left-unit q

  trans-cst≡₀id : {a b c : A} (p : b ≡ c) (q : a ≡₀ b)
    → transport (λ x → a ≡₀ x) p q ≡ q ∘₀ proj p
  trans-cst≡₀id (refl _) q = ! $ refl₀-right-unit q

  ap₀-compose : ∀ {j k} {B : Set j} {C : Set k} (g : B → C) (f : A → B)
    {x y : A} (p : x ≡₀ y) → ap₀ (g ◯ f) p ≡ ap₀ g (ap₀ f p)
  ap₀-compose f g =
    π₀-extend ⦃ λ _ → ≡-is-set $ π₀-is-set _ ⦄ (λ p →
      ap proj $ ap-compose f g p)
