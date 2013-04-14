{-# OPTIONS --without-K #-}

module lib.Int where

open import lib.Base
open import lib.Nat

data ℤ : Type₀ where
  O : ℤ
  pos : (n : ℕ) → ℤ
  neg : (n : ℕ) → ℤ
