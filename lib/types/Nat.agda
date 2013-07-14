{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.NType

module lib.types.Nat where

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


private
  ℕ-get-S : ℕ → ℕ
  ℕ-get-S 0 = 42
  ℕ-get-S (S n) = n

  S-injective : (n m : ℕ) (p : S n == S m) → n == m
  S-injective n m p = ap ℕ-get-S p

  ℕ-S≠O-type : ℕ → Set
  ℕ-S≠O-type O = Empty
  ℕ-S≠O-type (S n) = Unit

abstract
  ℕ-S≠O : (n : ℕ) → S n ≠ O
  ℕ-S≠O n p = transport ℕ-S≠O-type p unit

  ℕ-S≠O#instance : {n : ℕ} → (S n ≠ O)
  ℕ-S≠O#instance {n} = ℕ-S≠O n

  ℕ-O≠S : (n : ℕ) → (O ≠ S n)
  ℕ-O≠S n p = ℕ-S≠O n (! p)

  ℕ-has-dec-eq : has-dec-eq ℕ
  ℕ-has-dec-eq O O = inl idp
  ℕ-has-dec-eq O (S n) = inr (ℕ-O≠S n)
  ℕ-has-dec-eq (S n) O = inr (ℕ-S≠O n)
  ℕ-has-dec-eq (S n) (S m) with ℕ-has-dec-eq n m
  ℕ-has-dec-eq (S n) (S m) | inl p = inl (ap S p)
  ℕ-has-dec-eq (S n) (S m) | inr p⊥ = inr (λ p → p⊥ (S-injective n m p))

  ℕ-is-set : is-set ℕ
  ℕ-is-set = dec-eq-is-set ℕ-has-dec-eq

ℕ-level = ℕ-is-set
