{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Nat

module lib.types.Int where

data ℤ : Type₀ where
  O : ℤ
  pos : (n : ℕ) → ℤ
  neg : (n : ℕ) → ℤ

Int = ℤ

succ : ℤ → ℤ
succ O = pos O
succ (pos n) = pos (S n)
succ (neg O) = O
succ (neg (S n)) = neg n

pred : ℤ → ℤ
pred O = neg O
pred (pos O) = O
pred (pos (S n)) = pos n
pred (neg n) = neg (S n)

abstract
  succ-pred : (n : ℤ) → succ (pred n) == n
  succ-pred O = idp
  succ-pred (pos O) = idp
  succ-pred (pos (S n)) = idp
  succ-pred (neg n) = idp

  pred-succ : (n : ℤ) → pred (succ n) == n
  pred-succ O = idp
  pred-succ (pos n) = idp
  pred-succ (neg O) = idp
  pred-succ (neg (S n)) = idp

succ-equiv : ℤ ≃ ℤ
succ-equiv = equiv succ pred succ-pred pred-succ

postulate
  ℤ-is-set : is-set ℤ
