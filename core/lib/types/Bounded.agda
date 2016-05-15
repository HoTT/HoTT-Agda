{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.Relation
open import lib.NType
open import lib.types.Nat

module lib.types.Bounded where

-- [Bounded n] contains [n], which is different from [Fin]
data Bounded : ℕ → Type₀ where
  O : ∀ {n} → Bounded n
  S : ∀ {n} → Bounded n → Bounded (S n)

B-lift : ∀ {n m} → Bounded m → Bounded (n + m)
B-lift {n}   {m} O = O
B-lift {n} {S m} (S k) = transport! Bounded (+-βr n m) $ S (B-lift {n} {m} k)

infixl 80 _B+_
_B+_ : ∀ {n m} → Bounded n → Bounded m → Bounded (n + m)
_B+_   {n} {m}    O  l = B-lift {n} {m} l
_B+_ {S n} {m} (S k) l = S (k B+ l)

infixl 80 _-B_
_-B_ : (n : ℕ) → (m : Bounded n) → ℕ
n -B O = n
(S m) -B (S n) = m -B n
