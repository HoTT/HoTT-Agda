{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NConnected
open import lib.types.Nat
open import lib.types.TLevel
open import lib.types.Pointed
open import lib.types.Suspension

module lib.types.IteratedSuspension where

Ptd-Susp^ : ∀ {i} (n : ℕ) → Ptd i → Ptd i
Ptd-Susp^ O X = X
Ptd-Susp^ (S n) X = Ptd-Susp (Ptd-Susp^ n X)

Ptd-Susp^-conn : ∀ {i} (n : ℕ) {X : Ptd i} {m : ℕ₋₂}
  → is-connected m (fst X) → is-connected ((n -2) +2+ m) (fst (Ptd-Susp^ n X))
Ptd-Susp^-conn O cX = cX
Ptd-Susp^-conn (S n) cX = Susp-conn (Ptd-Susp^-conn n cX)


Ptd-Sphere : (n : ℕ) → Ptd₀
Ptd-Sphere n = Ptd-Susp^ n Ptd-Bool

Sphere : (n : ℕ) → Type₀
Sphere n = fst (Ptd-Sphere n)
