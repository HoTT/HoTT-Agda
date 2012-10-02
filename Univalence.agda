{-# OPTIONS --without-K #-}

open import Types
open import Functions
open import Paths
open import Equivalences

module Univalence where

id-is-equiv : ∀ {i} (A : Set i) → is-equiv (idmap A)
id-is-equiv A =
  λ y → ((y , refl y) ,
         (λ y' → total-path (π₂ y')
                            (trans-x≡a (π₂ y') (π₂ y')
                            ∘ opposite-left-inverse (π₂ y'))))

id-equiv : ∀ {i} (A : Set i) → A ≃ A
id-equiv A = (idmap A , id-is-equiv A)

path-to-eq : ∀ {i} {A B : Set i} → (A ≡ B → A ≃ B)
path-to-eq (refl A) = id-equiv A

postulate  -- Univalence axiom
  univalence : ∀ {i} (A B : Set i) → is-equiv (path-to-eq {i} {A} {B})

eq-to-path : ∀ {i} {A B : Set i} → (A ≃ B → A ≡ B)
eq-to-path {i} {A} {B} = inverse (path-to-eq , univalence A B)

eq-to-path-right-inverse : ∀ {i} {A B : Set i} (f : A ≃ B)
  → path-to-eq (eq-to-path f) ≡ f
eq-to-path-right-inverse f =
  inverse-right-inverse (path-to-eq , univalence _ _) f

-- Transport in the structural fibration of a universe

trans-X : ∀ {i} {A B : Set i} (f : A ≡ B) (u : A)
  → transport (λ X → X) f u ≡ ((path-to-eq f) $ u)
trans-X (refl _) u = refl u

trans-X-eq-to-path : ∀ {i} {A B : Set i} (f : A ≃ B) (u : A)
  → transport (λ X → X) (eq-to-path f) u ≡ (f $ u)
trans-X-eq-to-path {i} {A} {B} f u =
  trans-X (eq-to-path f) u
  ∘ map (λ (t : A ≃ B) → t $ u) (eq-to-path-right-inverse f)

trans-X→A : ∀ {i j} (A : Set j) {X Y : Set i} (e : X ≡ Y) (f : X → A)
  (a : Y) → transport (λ (X : Set i) → X → A) e f a
    ≡ f (inverse (path-to-eq e) a)
trans-X→A A (refl _) f a = refl _

trans-X→A-eq-to-path : ∀ {i j} (A : Set j) {X Y : Set i} (e : X ≃ Y)
  (f : X → A) (a : Y)
  → transport (λ (X : Set i) → X → A) (eq-to-path e) f a ≡ f (inverse e a)
trans-X→A-eq-to-path A e f a =
  trans-X→A A (eq-to-path e) f a
  ∘ map (λ u → f (inverse u a)) (eq-to-path-right-inverse e)

trans-A→X : ∀ {i j} (A : Set j) {X Y : Set i} (e : X ≡ Y) (f : A → X)
  (a : A) → transport (λ (X : Set i) → A → X) e f a
    ≡ π₁ (path-to-eq e) (f a)
trans-A→X A (refl _) f a = refl _

trans-A→X-eq-to-path : ∀ {i j} (A : Set j) {X Y : Set i} (e : X ≃ Y)
  (f : A → X) (a : A)
  → transport (λ (X : Set i) → A → X) (eq-to-path e) f a ≡ π₁ e (f a)
trans-A→X-eq-to-path A e f a =
  trans-A→X A (eq-to-path e) f a
  ∘ map (λ u → π₁ u (f a)) (eq-to-path-right-inverse e)

-- Induction along equivalences

equiv-induction : ∀ {i j} (P : (A : Set i) (B : Set i) (f : A ≃ B) → Set j)
  (d : (A : Set i) → P A A (id-equiv A)) (A B : Set i) (f : A ≃ B)
  → P A B f
equiv-induction P d A B f =
  transport (P A B) (eq-to-path-right-inverse f)
    (equiv-induction-int P d A B (eq-to-path f)) where

  equiv-induction-int : ∀ {i j}
    (P : (A : Set i) (B : Set i) (f : A ≃ B) → Set j)
    (d : (A : Set i) → P A A (id-equiv A)) (A B : Set i) (p : A ≡ B)
    → P A B (path-to-eq p)
  equiv-induction-int P d .A .A (refl A) = d A

