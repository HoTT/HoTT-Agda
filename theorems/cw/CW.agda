{-# OPTIONS --without-K #-}

{-
  Adapted from Ulrik's work in Lean (released under Apache License 2.0)
  https://github.com/leanprover/lean/blob/master/hott/homotopy/cellcomplex.hlean
-}

open import HoTT

module cw.CW where

attach-span : ∀ {i j k} {A : Type i} {B : Type j}
  (n : ℕ) (boundary : A × Sphere {k} n → B) → Span {i} {j} {lmax i k}
attach-span {A = A} {B} n boundary = span A B (A × Sphere n) fst boundary

Attach : ∀ {i j k} {A : Type i} {B : Type j}
  (n : ℕ) (boundary : A × Sphere {k} n → B) → Type (lmax i (lmax j k))
Attach {A = A} {B} n boundary = Pushout (attach-span {A = A} {B} n boundary)

Skeleton : ∀ {i} → ℕ → Type (lsucc i)
realizer : ∀ {i} {n : ℕ} → Skeleton {i} n → Type i

Skeleton {i} O = Type i
Skeleton {i} (S n) = Σ (Skeleton {i} n) (λ s → Σ (Type i) λ A → A × Sphere {i} n → realizer s)

realizer {n = O} A = A
realizer {n = S n} (s , (A , boundary)) = Attach n boundary

⟦_⟧ = realizer
