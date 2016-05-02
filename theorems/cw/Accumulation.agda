{-# OPTIONS --without-K #-}

open import HoTT
open import cw.CW

module cw.Accumulation where

  cw-incl : ∀ (n m : ℕ) → (le : n ≤ m) → Skeleton n → Skeleton m

