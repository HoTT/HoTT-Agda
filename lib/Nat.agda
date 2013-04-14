{-# OPTIONS --without-K #-}

module lib.Nat where

open import lib.Base

data ℕ : Type₀ where
  O : ℕ
  S : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO O #-}
{-# BUILTIN SUC S #-}

Nat = ℕ

_+_ : ℕ → ℕ → ℕ
0 + n = n
(S m) + n = S (m + n)
