{-# OPTIONS --without-K #-}

open import Types
open import Paths

module Contractible where

is-contr : ∀ {i} (A : Set i) → Set i
is-contr A = Σ A (λ x → ((y : A) → y ≡ x))

-- The identity types of a contractible type is contractible

is-contr-path : ∀ {i} (A : Set i) (c : is-contr A) (x y : A) → x ≡ y
is-contr-path A c x y = π₂ c x ∘ (! (π₂ c y))

is-contr-unique-path : ∀ {i} (A : Set i) (c : is-contr A) {x y : A} (p : x ≡ y)
  → p ≡ is-contr-path A c x y
is-contr-unique-path A c (refl _) = ! (opposite-right-inverse (π₂ c _))

abstract
  path-contr-contr : ∀ {i} (A : Set i) (c : is-contr A) (x y : A)
    → is-contr (x ≡ y)
  path-contr-contr A c x y = (is-contr-path A c x y , is-contr-unique-path A c)

-- Unit is contractible
unit-is-contr : ∀ {i} → is-contr (unit {i})
unit-is-contr = (tt , λ y → refl tt)

-- The type of paths to a fixed point is contractible
pathto-unique-path : ∀ {i} {A : Set i} {x : A} (pp : Σ A (λ t → t ≡ x))
  → pp ≡ (x , refl x)
pathto-unique-path (.x , refl x) = refl _

pathto-is-contr : ∀ {i} {A : Set i} (x : A) → is-contr (Σ A (λ t → t ≡ x))
pathto-is-contr x = ((x , refl x) , pathto-unique-path)

