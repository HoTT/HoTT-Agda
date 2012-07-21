{-# OPTIONS --without-K #-}

open import Base
open import Truncation.Truncation
open import Truncation.TruncationUP

module Truncation.Functor (n : ℕ) ⦃ >0 : n ≢ O ⦄ where

mapτ : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → τ n A → τ n B
mapτ {A = A} {B = B} f = τ-extend-nondep n (λ x → proj n B (f x)) where
  hlevel-τnB : is-hlevel n (τ n B)
  hlevel-τnB = τ-hlevel n B

compose-mapτ : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} (f : A → B) (g : B → C) → (mapτ g ◯ mapτ f ≡ mapτ (g ◯ f))
compose-mapτ f g = funext (τ-extend n ⦃ p = λ x → is-increasing-hlevel n _ (τ-hlevel n _) _ _ ⦄ (λ x → refl _))

mapτ-id : ∀ {i} (A : Set i) → mapτ (λ (x : A) → x) ≡ λ (x : τ n A) → x
mapτ-id A = funext (τ-extend n ⦃ p = λ x → is-increasing-hlevel n _ (τ-hlevel n _) _ _ ⦄ (λ x → refl _))

-- open Map public

-- module Functoriality {i j k : Level} (A : Set i) (B : Set j) (C : Set k) where
--   module τA = Truncation.Truncation 0 A
--   module τB = Truncation.Truncation 0 B
--   module τC = Truncation.Truncation 0 C
