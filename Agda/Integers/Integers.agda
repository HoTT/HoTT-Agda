{-# OPTIONS --without-K #-}

open import Homotopy

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

-- Equality on ℕ and ℤ is decidable and both are sets

ℕ-get-S : ℕ → ℕ
ℕ-get-S 0 = 0
ℕ-get-S (S n) = n

ℕ-get-S-S : (n : ℕ) → ℕ-get-S (S n) ≡ n
ℕ-get-S-S 0 = refl 0
ℕ-get-S-S (S n) = refl (S n)

S-injective : (n m : ℕ) (p : S n ≡ S m) → n ≡ m
S-injective n m p = ! (ℕ-get-S-S n) ∘ (map ℕ-get-S p ∘ ℕ-get-S-S m)

ℕ-dec-eq : dec-eq ℕ
ℕ-dec-eq O O = inl (refl O)
ℕ-dec-eq O (S y) = inr (λ ())
ℕ-dec-eq (S y) O = inr (λ ())
ℕ-dec-eq (S y) (S y') with ℕ-dec-eq y y'
ℕ-dec-eq (S y) (S y') | inl p = inl (map S p)
ℕ-dec-eq (S y) (S y') | inr p⊥ = inr (λ p → p⊥ (S-injective y y' p))

is-set-ℕ : is-set ℕ
is-set-ℕ = dec-eq-is-set ℕ ℕ-dec-eq

ℤ-get-pos : ℤ → ℕ
ℤ-get-pos O = 0
ℤ-get-pos (pos n) = n
ℤ-get-pos (neg n) = 0

ℤ-get-pos-pos : (n : ℕ) → ℤ-get-pos (pos n) ≡ n
ℤ-get-pos-pos 0 = refl _
ℤ-get-pos-pos (S n) = refl _

pos-injective : (n m : ℕ) (p : pos n ≡ pos m) → n ≡ m
pos-injective n m p = ! (ℤ-get-pos-pos n) ∘ (map ℤ-get-pos p ∘ ℤ-get-pos-pos m)

ℤ-get-neg : ℤ → ℕ
ℤ-get-neg O = 0
ℤ-get-neg (pos n) = 0
ℤ-get-neg (neg n) = n

ℤ-get-neg-neg : (n : ℕ) → ℤ-get-neg (neg n) ≡ n
ℤ-get-neg-neg 0 = refl _
ℤ-get-neg-neg (S n) = refl _

neg-injective : (n m : ℕ) (p : neg n ≡ neg m) → n ≡ m
neg-injective n m p = ! (ℤ-get-neg-neg n) ∘ (map ℤ-get-neg p ∘ ℤ-get-neg-neg m)

ℤ-dec-eq : dec-eq ℤ
ℤ-dec-eq O O = inl (refl O)
ℤ-dec-eq O (pos y) = inr (λ ())
ℤ-dec-eq O (neg y) = inr (λ ())
ℤ-dec-eq (pos y) O = inr (λ ())
ℤ-dec-eq (pos y) (pos y') with ℕ-dec-eq y y'
ℤ-dec-eq (pos y) (pos y') | inl p = inl (map pos p)
ℤ-dec-eq (pos y) (pos y') | inr p⊥ = inr (λ p → p⊥ (pos-injective y y' p))
ℤ-dec-eq (pos y) (neg y') = inr (λ ())
ℤ-dec-eq (neg y) O = inr (λ ())
ℤ-dec-eq (neg y) (pos y') = inr (λ ())
ℤ-dec-eq (neg y) (neg y') with ℕ-dec-eq y y'
ℤ-dec-eq (neg y) (neg y') | inl p = inl (map neg p)
ℤ-dec-eq (neg y) (neg y') | inr p⊥ = inr (λ p → p⊥ (neg-injective y y' p))

is-set-ℤ : is-set ℤ
is-set-ℤ = dec-eq-is-set ℤ ℤ-dec-eq