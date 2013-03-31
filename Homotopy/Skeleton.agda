{-# OPTIONS --without-K #-}

open import Base

module Homotopy.Skeleton where

private
  module Graveyard {i} {A B : Set i} {f : A → B} where
    private
      data #skeleton₁ : Set i where
        #point : A → #skeleton₁

    skeleton₁ : Set i
    skeleton₁ = #skeleton₁

    point : A → skeleton₁
    point = #point

    postulate  -- HIT
      link : ∀ a₁ a₂ → f a₁ ≡ f a₂ → point a₁ ≡ point a₂

    skeleton₁-rec : ∀ {l} (P : skeleton₁ → Set l)
      (point* : ∀ a → P (point a))
      (link* : ∀ a₁ a₂ (p : f a₁ ≡ f a₂)
        → transport P (link a₁ a₂ p) (point* a₁) ≡ point* a₂)
      → (x : skeleton₁) → P x
    skeleton₁-rec P point* link* (#point a) = point* a

    postulate  -- HIT
      skeleton₁-β-link : ∀ {l} (P : skeleton₁ → Set l)
        (point* : ∀ a → P (point a))
        (link* : ∀ a₁ a₂ (p : f a₁ ≡ f a₂)
          → transport P (link a₁ a₂ p) (point* a₁) ≡ point* a₂)
        a₁ a₂ (p : f a₁ ≡ f a₂)
        → apd (skeleton₁-rec {l} P point* link*) (link a₁ a₂ p)
        ≡ link* a₁ a₂ p

    skeleton₁-rec-nondep : ∀ {l} (P : Set l) (point* : A → P)
      (link* : ∀ a₁ a₂ → f a₁ ≡ f a₂ → point* a₁ ≡ point* a₂)
      → (skeleton₁ → P)
    skeleton₁-rec-nondep P point* link* (#point a) = point* a

    postulate  -- HIT
      skeleton₁-β-link-nondep : ∀ {l} (P : Set l) (point* : A → P)
        (link* : ∀ a₁ a₂ → f a₁ ≡ f a₂ → point* a₁ ≡ point* a₂)
        a₁ a₂ (p : f a₁ ≡ f a₂)
        → ap (skeleton₁-rec-nondep P point* link*) (link a₁ a₂ p)
        ≡ link* a₁ a₂ p

open Graveyard public hiding (skeleton₁)

module _ {i} {A B : Set i} where
  skeleton₁ : (A → B) → Set i
  skeleton₁ f = Graveyard.skeleton₁ {i} {A} {B} {f}

  skeleton₁-lifted : ∀ {f} → skeleton₁ f → B
  skeleton₁-lifted {f} = skeleton₁-rec-nondep B f (λ _ _ p → p)
