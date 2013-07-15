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

{- Proof that [ℤ] has decidable equality and hence is a set -}

private
  ℤ-get-pos : ℤ → ℕ
  ℤ-get-pos O = 0
  ℤ-get-pos (pos n) = n
  ℤ-get-pos (neg n) = 0

  pos-injective : (n m : ℕ) (p : pos n == pos m) → n == m
  pos-injective n m p = ap ℤ-get-pos p

  ℤ-get-neg : ℤ → ℕ
  ℤ-get-neg O = 0
  ℤ-get-neg (pos n) = 0
  ℤ-get-neg (neg n) = n

  neg-injective : (n m : ℕ) (p : neg n == neg m) → n == m
  neg-injective n m p = ap ℤ-get-neg p

  ℤ-neg≠O≠pos-type : ℤ → Type₀
  ℤ-neg≠O≠pos-type O = Unit
  ℤ-neg≠O≠pos-type (pos n) = Empty
  ℤ-neg≠O≠pos-type (neg n) = Empty

  ℤ-neg≠pos-type : ℤ → Type₀
  ℤ-neg≠pos-type O = Unit
  ℤ-neg≠pos-type (pos n) = Empty
  ℤ-neg≠pos-type (neg n) = Unit

abstract
  ℤ-O≠pos : (n : ℕ) → O ≠ pos n
  ℤ-O≠pos n p = transport ℤ-neg≠O≠pos-type p unit

  ℤ-pos≠O : (n : ℕ) → pos n ≠ O
  ℤ-pos≠O n p = transport ℤ-neg≠O≠pos-type (! p) unit

  ℤ-O≠neg : (n : ℕ) → O ≠ neg n
  ℤ-O≠neg n p = transport ℤ-neg≠O≠pos-type p unit

  ℤ-neg≠O : (n : ℕ) → neg n ≠ O
  ℤ-neg≠O n p = transport ℤ-neg≠O≠pos-type (! p) unit

  ℤ-neg≠pos : (n m : ℕ) → neg n ≠ pos m
  ℤ-neg≠pos n m p = transport ℤ-neg≠pos-type p unit

  ℤ-pos≠neg : (n m : ℕ) → pos n ≠ neg m
  ℤ-pos≠neg n m p = transport ℤ-neg≠pos-type (! p) unit

  ℤ-has-dec-eq : has-dec-eq ℤ
  ℤ-has-dec-eq O O = inl idp
  ℤ-has-dec-eq O (pos n) = inr (ℤ-O≠pos n)
  ℤ-has-dec-eq O (neg n) = inr (ℤ-O≠neg n)
  ℤ-has-dec-eq (pos n) O = inr (ℤ-pos≠O n)
  ℤ-has-dec-eq (pos n) (pos m) with ℕ-has-dec-eq n m
  ℤ-has-dec-eq (pos n) (pos m) | inl p = inl (ap pos p)
  ℤ-has-dec-eq (pos n) (pos m) | inr p⊥ = inr (λ p → p⊥ (pos-injective n m p))
  ℤ-has-dec-eq (pos n) (neg m) = inr (ℤ-pos≠neg n m)
  ℤ-has-dec-eq (neg n) O = inr (ℤ-neg≠O n)
  ℤ-has-dec-eq (neg n) (pos m) = inr (ℤ-neg≠pos n m)
  ℤ-has-dec-eq (neg n) (neg m) with ℕ-has-dec-eq n m
  ℤ-has-dec-eq (neg n) (neg m) | inl p = inl (ap neg p)
  ℤ-has-dec-eq (neg n) (neg m) | inr p⊥ = inr (λ p → p⊥ (neg-injective n m p))

  ℤ-is-set : is-set ℤ
  ℤ-is-set = dec-eq-is-set ℤ-has-dec-eq

ℤ-level = ℤ-is-set
