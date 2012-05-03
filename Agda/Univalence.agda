{-# OPTIONS --without-K #-}

open import Types
open import Paths
open import Equivalences

module Univalence where

id-is-equiv : {i : Level} (A : Set i) → is-equiv (λ (x : A) → x)
id-is-equiv A = λ y → ((y , refl y) , (λ y' → total-path (π₂ y') (trans-x≡a (π₂ y') (π₂ y') ∘ opposite-left-inverse (π₂ y'))))

id-eq : {i : Level} (A : Set i) → A ≃ A
id-eq A = ((λ x → x) , id-is-equiv A)

path-to-eq : {i : Level} {A B : Set i} → (A ≡ B → A ≃ B)
path-to-eq (refl A) = id-eq A

postulate  -- Univalence axiom
  univalence : {i : Level} (A B : Set i) → is-equiv (path-to-eq {i} {A} {B})

eq-to-path : {i : Level} {A B : Set i} → (A ≃ B → A ≡ B)
eq-to-path {i} {A} {B} = inverse (path-to-eq , univalence A B)

eq-to-path-right-inverse : {i : Level} {A B : Set i} (f : A ≃ B) → path-to-eq (eq-to-path f) ≡ f
eq-to-path-right-inverse f = inverse-right-inverse (path-to-eq , univalence _ _) f

-- Transport in the structural fibration of a universe

trans-X : {i : Level} {A B : Set i} (f : A ≡ B) (u : A) → transport (λ X → X) f u ≡ ((path-to-eq f) $ u)
trans-X (refl _) u = refl u

trans-eq-to-path : {i : Level} {A B : Set i} (f : A ≃ B) (u : A) → transport (λ X → X) (eq-to-path f) u ≡ (f $ u)
trans-eq-to-path {i} {A} {B} f u = trans-X (eq-to-path f) u ∘ map (λ (t : A ≃ B) → t $ u) (eq-to-path-right-inverse f)

-- Induction along equivalences

equiv-induction : {i j : Level} (P : (A : Set i) (B : Set i) (f : A ≃ B) → Set j) (d : (A : Set i) → P A A (id-eq A)) →
  (A B : Set i) (f : A ≃ B) → P A B f
equiv-induction P d A B f = transport (P A B) (eq-to-path-right-inverse f) (equiv-induction-int P d A B (eq-to-path f)) where

  equiv-induction-int : {i j : Level} (P : (A : Set i) (B : Set i) (f : A ≃ B) → Set j) (d : (A : Set i) → P A A (id-eq A)) →
    (A B : Set i) (p : A ≡ B) → P A B (path-to-eq p)
  equiv-induction-int P d .A .A (refl A) = d A

