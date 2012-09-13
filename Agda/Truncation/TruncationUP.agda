{-# OPTIONS --without-K #-}

open import Base
open import Topology.Spheres
open import Topology.Suspension
open import Truncation.Truncation
open import Truncation.SphereFillings

module Truncation.TruncationUP where

-- By definition, truncation has n-spheres filled
τ-has-n-spheres-filled : ∀ {i} (n : ℕ) (A : Set i)
  → has-n-spheres-filled n (τ n A)
τ-has-n-spheres-filled n A = λ f → (top n A f , rays n A f)

-- Hence the nth truncation is of h-level [n]
abstract
  τ-hlevel : ∀ {i} (n : ℕ) ⦃ >0 : n ≢ 0 ⦄ (A : Set i) → is-hlevel n (τ n A)
  τ-hlevel n A = n-spheres-filled-hlevel n (τ n A) (τ-has-n-spheres-filled n A)

-- We can extend a function to the truncation, if the codomain is of the correct
-- hlevel
τ-extend : ∀ {i j} (n : ℕ) ⦃ >0 : n ≢ 0 ⦄ {A : Set i} {P : (τ n A) → Set j}
  ⦃ p : (x : τ n A) → is-hlevel n (P x) ⦄ (f : (x : A) → P (proj _ _ x))
  → ((x : τ n A) → P x)
τ-extend n {A = A} {P = P} ⦃ p ⦄ f =
  τ-rec _ _ _ f (λ f₁ p₁ → π₁ (u f₁ p₁)) (λ f₁ p₁ → π₂ (u f₁ p₁)) where
  u : _
  u = hlevel-n-has-filling-dep (τ n A) P n (λ f → (top n A f , rays n A f))

τ-extend-nondep : ∀ {i j} (n : ℕ) ⦃ >0 : n ≢ 0 ⦄ {A : Set i} {B : Set j}
  ⦃ p : is-hlevel n B ⦄ → ((f : A → B) → (τ n A → B))
τ-extend-nondep n {A = A} {B = B} ⦃ p = p ⦄ f =
  τ-rec-nondep n A B f (λ p → π₁ (u p)) (λ p₁ → π₂ (u p₁)) where
  u : _
  u = hlevel-n-has-n-spheres-filled n B p

-- Universal property of the truncation
abstract
  τ-up : ∀ {i j} (n : ℕ) ⦃ >0 : n ≢ 0 ⦄ (A : Set i) (B : Set j)
  ⦃ p : is-hlevel n B ⦄ → is-equiv (λ (f : τ n A → B) → (λ x → f (proj n A x)))
  τ-up n A B ⦃ p ⦄ = iso-is-eq _
    (τ-extend-nondep n)
    refl
    (λ f → funext (τ-extend n ⦃ p = λ x → lemma _ _ p ⦄ (λ x → refl _))) where

    lemma : (x y : B) (p : is-hlevel n B) → is-hlevel n (x ≡ y)
    lemma x y p with n
    lemma x y p | O = path-contr-contr B p x y
    lemma x y p | (S n) = is-increasing-hlevel n (x ≡ y) (p x y)

-- Equivalence associated to the universal property
τ-equiv : ∀ {i j} (n : ℕ) ⦃ >0 : n ≢ 0 ⦄ (A : Set i) (B : Set j)
  ⦃ p : is-hlevel n B ⦄ → (τ n A → B) ≃ (A → B)
τ-equiv n A B = (_ , τ-up n _ _)

open import CategoryTheory.ReflectiveSubCategory

-- Reflective subcategory associated to the truncation
τ-rsc : ∀ {i} (n : ℕ) ⦃ >0 : n ≢ 0 ⦄ → rsc {i}
τ-rsc n = Rsc (is-hlevel n) (is-hlevel-is-prop n) (τ n) (proj n) (τ-hlevel n)
              (τ-up n)
