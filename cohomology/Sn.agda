{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.OrdinaryTheory

module cohomology.Sn {i} (OT : OrdinaryTheory i) where

open OrdinaryTheory OT

C-Sphere-≠ : (n : ℤ) (m : ℕ) → (n ≠ ℕ-to-ℤ m)
  → C n (Ptd-Sphere m) == LiftUnit-Group
C-Sphere-≠ n O neq = C-dimension n neq
C-Sphere-≠ n (S m) neq =
  ap (λ k → C k (Ptd-Sphere (S m))) (! (succ-pred n))
  ∙ C-Susp (pred n) (Ptd-Sphere m)
  ∙ C-Sphere-≠ (pred n) m (λ p → neq (pred-injective n (pos m) p))

C-Sphere-diag : (m : ℕ) → C (ℕ-to-ℤ m) (Ptd-Sphere m) == C O (Ptd-Sphere O)
C-Sphere-diag O = idp
C-Sphere-diag 1 = C-Susp O (Ptd-Sphere O)
C-Sphere-diag (S (S m)) =
  C-Susp (pos m) (Ptd-Sphere (S m)) ∙ C-Sphere-diag (S m)
