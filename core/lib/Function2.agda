{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Truncation

module lib.Function2 where

is-surj : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) → Type (lmax i j)
is-surj {A = A} f = ∀ b → Trunc -1 (hfiber f b)

