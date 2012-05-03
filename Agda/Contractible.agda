{-# OPTIONS --without-K #-}

open import Types
open import Paths

module Contractible where

is-contr : {i : Level} (A : Set i) → Set i
is-contr A = Σ A (λ x → ((y : A) → y ≡ x))

-- The path spaces of a contractible type is contractible

is-contr-path : {i : Level} (A : Set i) (c : is-contr A) (x y : A) → x ≡ y
is-contr-path A c x y = π₂ c x ∘ (! (π₂ c y))

is-contr-unique-path : {i : Level} (A : Set i) (c : is-contr A) {x y : A} (p : x ≡ y) → p ≡ is-contr-path A c x y
is-contr-unique-path A c (refl _) = ! (opposite-right-inverse (π₂ c _))

path-contr-contr : {i : Level} (A : Set i) (c : is-contr A) (x y : A) → is-contr (x ≡ y)
path-contr-contr A c x y = (is-contr-path A c x y , is-contr-unique-path A c)

-- Unit is contractible

is-contr-unit : {i : Level} → is-contr (unit {i})
is-contr-unit = (tt , λ y → refl tt)

-- The type of paths with one end fixed is contractible
pathto-contr : {i : Level} {A : Set i} {x : A} (pp : Σ A (λ t → t ≡ x)) → pp ≡ (x , refl x)
pathto-contr (.x , refl x) = refl _

