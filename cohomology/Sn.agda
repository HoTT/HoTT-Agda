{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.Theory

module cohomology.Sn {i} (OT : OrdinaryTheory i) where

open OrdinaryTheory OT

C-Sphere-≠ : (n : ℤ) (m : ℕ) → (n ≠ ℕ-to-ℤ m)
  → C n (⊙Sphere m) == LiftUnit-Group
C-Sphere-≠ n O neq = C-dimension n neq
C-Sphere-≠ n (S m) neq =
  ap (λ k → C k (⊙Sphere (S m))) (! (succ-pred n))
  ∙ group-ua (C-Susp (pred n) (⊙Sphere m))
  ∙ C-Sphere-≠ (pred n) m (λ p → neq (pred-injective n (pos m) p))

C-Sphere-diag : (m : ℕ) → C (ℕ-to-ℤ m) (⊙Sphere m) == C O (⊙Sphere O)
C-Sphere-diag O = idp
C-Sphere-diag 1 = group-ua (C-Susp O (⊙Sphere O))
C-Sphere-diag (S (S m)) =
  group-ua (C-Susp (pos m) (⊙Sphere (S m))) ∙ C-Sphere-diag (S m)
