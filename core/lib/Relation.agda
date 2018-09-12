{-# OPTIONS --without-K --rewriting #-}

open import lib.Base

module lib.Relation {i} where

Rel : ∀ (A : Type i) j → Type (lmax i (lsucc j))
Rel A j = A → A → Type j

empty-rel : ∀ {A : Type i} → Rel A lzero
empty-rel _ _ = Empty

module _ {A : Type i} {j} (rel : Rel A j) where

  Decidable : Type (lmax i j)
  Decidable = ∀ a₁ a₂ → Dec (rel a₁ a₂)

  is-refl : Type (lmax i j)
  is-refl = ∀ a → rel a a

  is-sym : Type (lmax i j)
  is-sym = ∀ {a b} → rel a b → rel b a

  is-trans : Type (lmax i j)
  is-trans = ∀ {a b c} → rel a b → rel b c → rel a c

  -- as equivalence relation
  -- is-equational : Type (lmax i j)
