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

-- Equality on ℕ and ℤ is decidable and both are sets

private
  ℕ-get-S : ℕ → ℕ
  ℕ-get-S 0 = 42
  ℕ-get-S (S n) = n

  S-injective : (n m : ℕ) (p : S n ≡ S m) → n ≡ m
  S-injective n m p = map ℕ-get-S p

  ℕ-Sn≢O-type : ℕ → Set
  ℕ-Sn≢O-type O = ⊥
  ℕ-Sn≢O-type (S n) = unit

abstract
  ℕ-Sn≢O : (n : ℕ) → (S n ≢ O)
  ℕ-Sn≢O n p = transport ℕ-Sn≢O-type p tt

  ℕ-dec-eq : dec-eq ℕ
  ℕ-dec-eq O O = inl (refl O)
  ℕ-dec-eq O (S n) = inr (λ p → ℕ-Sn≢O n (! p))
  ℕ-dec-eq (S n) O = inr (ℕ-Sn≢O n)
  ℕ-dec-eq (S n) (S m) with ℕ-dec-eq n m
  ℕ-dec-eq (S n) (S m) | inl p = inl (map S p)
  ℕ-dec-eq (S n) (S m) | inr p⊥ = inr (λ p → p⊥ (S-injective n m p))

  ℕ-is-set : is-set ℕ
  ℕ-is-set = dec-eq-is-set ℕ ℕ-dec-eq

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

  ℤ-O≢pos : (n : ℕ) → (O ≡ pos n → ⊥)
  ℤ-O≢pos n p = transport ℤ-neg≢O≢pos-type p tt

  ℤ-O≢neg : (n : ℕ) → (O ≡ neg n → ⊥)
  ℤ-O≢neg n p = transport ℤ-neg≢O≢pos-type p tt

  ℤ-neg≢pos-type : ℤ → Set
  ℤ-neg≢pos-type O = unit
  ℤ-neg≢pos-type (pos n) = ⊥
  ℤ-neg≢pos-type (neg n) = unit

  ℤ-neg≢pos : (n m : ℕ) → (neg n ≡ pos m → ⊥)
  ℤ-neg≢pos n m p = transport ℤ-neg≢pos-type p tt

abstract
  ℤ-dec-eq : dec-eq ℤ
  ℤ-dec-eq O O = inl (refl O)
  ℤ-dec-eq O (pos n) = inr (ℤ-O≢pos n)
  ℤ-dec-eq O (neg n) = inr (ℤ-O≢neg n)
  ℤ-dec-eq (pos n) O = inr (λ p → ℤ-O≢pos n (! p))
  ℤ-dec-eq (pos n) (pos m) with ℕ-dec-eq n m
  ℤ-dec-eq (pos n) (pos m) | inl p = inl (map pos p)
  ℤ-dec-eq (pos n) (pos m) | inr p⊥ = inr (λ p → p⊥ (pos-injective n m p))
  ℤ-dec-eq (pos n) (neg m) = inr (λ p → ℤ-neg≢pos m n (! p))
  ℤ-dec-eq (neg n) O = inr (λ p → ℤ-O≢neg n (! p))
  ℤ-dec-eq (neg n) (pos m) = inr (ℤ-neg≢pos n m)
  ℤ-dec-eq (neg n) (neg m) with ℕ-dec-eq n m
  ℤ-dec-eq (neg n) (neg m) | inl p = inl (map neg p)
  ℤ-dec-eq (neg n) (neg m) | inr p⊥ = inr (λ p → p⊥ (neg-injective n m p))
  
  ℤ-is-set : is-set ℤ
  ℤ-is-set = dec-eq-is-set ℤ ℤ-dec-eq
