{-# OPTIONS --without-K #-}

open import Types
open import Paths
open import Equivalences
open import Univalence

module Integers.Integers where

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

succ-pred : (t : ℤ) → succ (pred t) ≡ t
succ-pred O = refl O
succ-pred (pos O) = refl (pos O)
succ-pred (pos (S y)) = refl (pos (S y))
succ-pred (neg y) = refl (neg y)

pred-succ : (t : ℤ) → pred (succ t) ≡ t
pred-succ O = refl O
pred-succ (pos y) = refl (pos y)
pred-succ (neg O) = refl (neg O)
pred-succ (neg (S y)) = refl (neg (S y))

succ-is-equiv : is-equiv succ
succ-is-equiv = iso-is-eq succ pred succ-pred pred-succ

succ-equiv : ℤ ≃ ℤ
succ-equiv = (succ , succ-is-equiv)

succ-path : ℤ ≡ ℤ
succ-path = eq-to-path succ-equiv