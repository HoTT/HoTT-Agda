{-# OPTIONS --without-K #-}

module lib.Pi where

open import lib.Base

Π : ∀ {i j} (A : Type i) (P : A → Type j) → Type (max i j)
Π A P = (x : A) → P x
