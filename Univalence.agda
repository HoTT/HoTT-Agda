{-# OPTIONS --without-K #-}

open import Types
open import Functions
open import Paths
open import HLevel
open import Equivalences

module Univalence {i} where

postulate  -- Univalence axiom
  univalence : (A B : Set i) → is-equiv (path-to-eq {i} {A} {B})

abstract
  -- It does not harm to have [eq-to-path] abstract even if its type is not a
  -- prop because the definition uses an axiom so there is no computational
  -- content anyway
  eq-to-path : {A B : Set i} → (A ≃ B → A ≡ B)
  eq-to-path {A} {B} = inverse (path-to-eq , univalence A B)

  eq-to-path-is-equiv : {A B : Set i} → is-equiv (eq-to-path {A} {B})
  eq-to-path-is-equiv = inverse-is-equiv (path-to-eq , univalence _ _)

  eq-to-path-right-inverse : {A B : Set i} (f : A ≃ B)
    → path-to-eq (eq-to-path f) ≡ f
  eq-to-path-right-inverse f =
    inverse-right-inverse (path-to-eq , univalence _ _) f

path-to-eq-equiv : {A B : Set i} → ((A ≡ B) ≃ (A ≃ B))
path-to-eq-equiv = (path-to-eq , univalence _ _)

eq-to-path-equiv : {A B : Set i} → ((A ≃ B) ≃ (A ≡ B))
eq-to-path-equiv = (eq-to-path , eq-to-path-is-equiv)

-- Transport in the structural fibration of a universe

trans-id : {A B : Set i} (f : A ≡ B) (u : A)
  → transport (λ X → X) f u ≡ (path-to-eq f) ☆ u
trans-id (refl _) u = refl u

trans-id-eq-to-path : {A B : Set i} (f : A ≃ B) (u : A)
  → transport (λ X → X) (eq-to-path f) u ≡ f ☆ u
trans-id-eq-to-path {A} {B} f u =
  trans-id (eq-to-path f) u
  ∘ map (λ (t : A ≃ B) → t ☆ u) (eq-to-path-right-inverse f)

-- Not used
--
-- trans-id→A : ∀ {i j} (A : Set j) {X Y : Set i} (e : X ≡ Y) (f : X → A)
--   (a : Y) → transport (λ (X : Set i) → X → A) e f a
--     ≡ f (inverse (path-to-eq e) a)
-- trans-id→A A (refl _) f a = refl _

-- trans-id→A-eq-to-path : ∀ {i j} (A : Set j) {X Y : Set i} (e : X ≃ Y)
--   (f : X → A) (a : Y)
--   → transport (λ (X : Set i) → X → A) (eq-to-path e) f a ≡ f (inverse e a)
-- trans-id→A-eq-to-path A e f a =
--   trans-id→A A (eq-to-path e) f a
--   ∘ map (λ u → f (inverse u a)) (eq-to-path-right-inverse e)

-- trans-cst→X : ∀ {i j} (A : Set j) {X Y : Set i} (e : X ≡ Y) (f : A → X)
--   (a : A) → transport (λ (X : Set i) → A → X) e f a
--     ≡ π₁ (path-to-eq e) (f a)
-- trans-cst→X A (refl _) f a = refl _

-- trans-cst→X-eq-to-path : ∀ {i j} (A : Set j) {X Y : Set i} (e : X ≃ Y)
--   (f : A → X) (a : A)
--   → transport (λ (X : Set i) → A → X) (eq-to-path e) f a ≡ π₁ e (f a)
-- trans-cst→X-eq-to-path A e f a =
--   trans-cst→X A (eq-to-path e) f a
--   ∘ map (λ u → π₁ u (f a)) (eq-to-path-right-inverse e)

-- Induction along equivalences

equiv-induction : ∀ {j} (P : {A B : Set i} (f : A ≃ B) → Set j)
  (d : (A : Set i) → P (id-equiv A)) {A B : Set i} (f : A ≃ B)
  → P f
equiv-induction P d f =
  transport P (eq-to-path-right-inverse f)
    (equiv-induction-int P d (eq-to-path f)) where

  equiv-induction-int : ∀ {j}
    (P : {A : Set i} {B : Set i} (f : A ≃ B) → Set j)
    (d : (A : Set i) → P (id-equiv A)) {A B : Set i} (p : A ≡ B)
    → P (path-to-eq p)
  equiv-induction-int P d (refl A) = d A
