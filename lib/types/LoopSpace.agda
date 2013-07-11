{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Nat
open import lib.types.TLevel
open import lib.types.Truncation

module lib.types.LoopSpace where

Ω^ : ∀ {i} (n : ℕ) (A : Type i) (a : A) → Type i
Ω^ O A a = A
Ω^ (S n) A a = Ω^ n (a == a) idp

idp^ : ∀ {i} (n : ℕ) (A : Type i) (a : A) → Ω^ n A a
idp^ O A a = a
idp^ (S n) A a = idp^ n (a == a) idp

π : ∀ {i} (n : ℕ) (A : Type i) (a : A) → Type i
π n A a = Trunc ⟨0⟩ (Ω^ n A a)

ap^ : ∀ {i j} (n : ℕ) {A : Type i} {B : Type j} {a : A}
 (f : A → B) → Ω^ n A a → Ω^ n B (f a)
ap^ O {a = a} f x = f x
ap^ (S n) {a = a} f p = ap^ n (ap f) p

Ω^-outer : ∀ {i} (n : ℕ) (A : Type i) (a : A) → Ω^ (S n) A a 
          == Path (idp^ n A a) (idp^ n A a)
Ω^-outer O A a = idp
Ω^-outer (S n) A a = Ω^-outer n (a == a) idp

Ω^-level-in : ∀ {i} (m : ℕ₋₂) (n : ℕ) (A : Type i) (a : A)
  → (has-level ((n -2) +2+ m) A → has-level m (Ω^ n A a))
Ω^-level-in m O A a pA = pA
Ω^-level-in m (S n) A a pA = Ω^-level-in m n (a == a) idp (pA a a)

-- Ω^-level-out : ∀ {i} (m : ℕ₋₂) (n : ℕ) (A : Type i) (a : A)
--   → (has-level m (Ω^ n A a) → has-level ((n -2) +2+ m) A)
-- Ω^-level-out m O A a pA = pA
-- Ω^-level-out m (S n) A a pA = {!!}

Ω^-–>-equiv : ∀ {i j} (n : ℕ) {A : Type i} {B : Type j} (e : A ≃ B) (a : A)
  → Ω^ n A a ≃ Ω^ n B (–> e a)
Ω^-–>-equiv O e a = e
Ω^-–>-equiv (S n) e a = Ω^-–>-equiv n (equiv-ap e a a) idp

Ω^-coe-path : ∀ {i} (n : ℕ) {A B : Type i} (p : A == B) (a : A)
  → Ω^ n A a == Ω^ n B (coe p a)
Ω^-coe-path _ idp _ = idp

Trunc-Ω^-equiv : ∀ {i} (m : ℕ₋₂) (n : ℕ) (A : Type i) (a : A)
  → Trunc m (Ω^ n A a) ≃ Ω^ n (Trunc ((n -2) +2+ m) A) [ a ]
Trunc-Ω^-equiv m O A a = ide _
Trunc-Ω^-equiv m (S n) A a = 
  Ω^-–>-equiv n ((Trunc=-equiv [ _ ] [ _ ])⁻¹) [ idp ] 
  ∘e (Trunc-Ω^-equiv m n (a == a) idp)

Trunc-Ω^-path : ∀ {i} (m : ℕ₋₂) (n : ℕ) (A : Type i) (a : A)
  → Trunc m (Ω^ n A a) == Ω^ n (Trunc ((n -2) +2+ m) A) [ a ]
Trunc-Ω^-path m n A a = ua $ (Trunc-Ω^-equiv m n A a)

