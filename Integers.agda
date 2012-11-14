{-# OPTIONS --without-K #-}

open import Base

module Integers where

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
  succ-pred : (n : ℤ) → succ (pred n) ≡ n
  succ-pred O = refl O
  succ-pred (pos O) = refl (pos O)
  succ-pred (pos (S n)) = refl (pos (S n))
  succ-pred (neg n) = refl (neg n)

  pred-succ : (n : ℤ) → pred (succ n) ≡ n
  pred-succ O = refl O
  pred-succ (pos n) = refl (pos n)
  pred-succ (neg O) = refl (neg O)
  pred-succ (neg (S n)) = refl (neg (S n))

  succ-is-equiv : is-equiv succ
  succ-is-equiv = iso-is-eq succ pred succ-pred pred-succ

succ-equiv : ℤ ≃ ℤ
succ-equiv = (succ , succ-is-equiv)

-- Equality on ℕ and ℤ is decidable and both are sets

private
  ℕ-get-S : ℕ → ℕ
  ℕ-get-S 0 = 42
  ℕ-get-S (S n) = n

  S-injective : (n m : ℕ) (p : S n ≡ S m) → n ≡ m
  S-injective n m p = map ℕ-get-S p

  ℕ-S≢O-type : ℕ → Set
  ℕ-S≢O-type O = ⊥
  ℕ-S≢O-type (S n) = unit

abstract
  ℕ-S≢O : (n : ℕ) → (S n ≢ O)
  ℕ-S≢O n p = transport ℕ-S≢O-type p tt

  ℕ-O≢S : (n : ℕ) → (O ≢ S n)
  ℕ-O≢S n p = ℕ-S≢O n (! p)

  ℕ-dec-eq : has-dec-eq ℕ
  ℕ-dec-eq O O = inl (refl O)
  ℕ-dec-eq O (S n) = inr (ℕ-O≢S n)
  ℕ-dec-eq (S n) O = inr (ℕ-S≢O n)
  ℕ-dec-eq (S n) (S m) with ℕ-dec-eq n m
  ℕ-dec-eq (S n) (S m) | inl p = inl (map S p)
  ℕ-dec-eq (S n) (S m) | inr p⊥ = inr (λ p → p⊥ (S-injective n m p))

  ℕ-is-set : is-set ℕ
  ℕ-is-set = dec-eq-is-set ℕ-dec-eq

private
  ℤ-get-pos : ℤ → ℕ
  ℤ-get-pos O = 0
  ℤ-get-pos (pos n) = n
  ℤ-get-pos (neg n) = 0
  
  pos-injective : (n m : ℕ) (p : pos n ≡ pos m) → n ≡ m
  pos-injective n m p = map ℤ-get-pos p
  
  ℤ-get-neg : ℤ → ℕ
  ℤ-get-neg O = 0
  ℤ-get-neg (pos n) = 0
  ℤ-get-neg (neg n) = n

  neg-injective : (n m : ℕ) (p : neg n ≡ neg m) → n ≡ m
  neg-injective n m p = map ℤ-get-neg p

  ℤ-neg≢O≢pos-type : ℤ → Set
  ℤ-neg≢O≢pos-type O = unit
  ℤ-neg≢O≢pos-type (pos n) = ⊥
  ℤ-neg≢O≢pos-type (neg n) = ⊥

  ℤ-neg≢pos-type : ℤ → Set
  ℤ-neg≢pos-type O = unit
  ℤ-neg≢pos-type (pos n) = ⊥
  ℤ-neg≢pos-type (neg n) = unit

abstract
  ℤ-O≢pos : (n : ℕ) → O ≢ pos n
  ℤ-O≢pos n p = transport ℤ-neg≢O≢pos-type p tt

  ℤ-pos≢O : (n : ℕ) → pos n ≢ O
  ℤ-pos≢O n p = transport ℤ-neg≢O≢pos-type (! p) tt

  ℤ-O≢neg : (n : ℕ) → O ≢ neg n
  ℤ-O≢neg n p = transport ℤ-neg≢O≢pos-type p tt

  ℤ-neg≢O : (n : ℕ) → neg n ≢ O
  ℤ-neg≢O n p = transport ℤ-neg≢O≢pos-type (! p) tt

  ℤ-neg≢pos : (n m : ℕ) → neg n ≢ pos m
  ℤ-neg≢pos n m p = transport ℤ-neg≢pos-type p tt

  ℤ-pos≢neg : (n m : ℕ) → pos n ≢ neg m
  ℤ-pos≢neg n m p = transport ℤ-neg≢pos-type (! p) tt

  ℤ-dec-eq : has-dec-eq ℤ
  ℤ-dec-eq O O = inl (refl O)
  ℤ-dec-eq O (pos n) = inr (ℤ-O≢pos n)
  ℤ-dec-eq O (neg n) = inr (ℤ-O≢neg n)
  ℤ-dec-eq (pos n) O = inr (ℤ-pos≢O n)
  ℤ-dec-eq (pos n) (pos m) with ℕ-dec-eq n m
  ℤ-dec-eq (pos n) (pos m) | inl p = inl (map pos p)
  ℤ-dec-eq (pos n) (pos m) | inr p⊥ = inr (λ p → p⊥ (pos-injective n m p))
  ℤ-dec-eq (pos n) (neg m) = inr (ℤ-pos≢neg n m)
  ℤ-dec-eq (neg n) O = inr (ℤ-neg≢O n)
  ℤ-dec-eq (neg n) (pos m) = inr (ℤ-neg≢pos n m)
  ℤ-dec-eq (neg n) (neg m) with ℕ-dec-eq n m
  ℤ-dec-eq (neg n) (neg m) | inl p = inl (map neg p)
  ℤ-dec-eq (neg n) (neg m) | inr p⊥ = inr (λ p → p⊥ (neg-injective n m p))

  ℤ-is-set : is-set ℤ
  ℤ-is-set = dec-eq-is-set ℤ-dec-eq
