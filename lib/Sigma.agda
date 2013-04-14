{-# OPTIONS --without-K #-}

module lib.Sigma where

open import lib.Base

record Σ {i j} (A : Type i) (B : A → Type j) : Type (max i j) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

pair : ∀ {i j} {A : Type i} {B : A → Type j} (a : A) (b : B a) → Σ A B
pair a b = (a , b)

-- Product
_×_ : ∀ {i j} (A : Type i) (B : Type j) → Type (max i j)
A × B = Σ A (λ _ → B)
