{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.Theory

module cohomology.Sn {i} (OT : OrdinaryTheory i) where

open OrdinaryTheory OT

C-Sphere-≠ : (n : ℤ) (m : ℕ) → (n ≠ ℕ-to-ℤ m)
  → C n (⊙Lift (⊙Sphere m)) == Lift-Unit-group
C-Sphere-≠ n O neq = C-dimension n neq
C-Sphere-≠ n (S m) neq =
  C n (⊙Lift (⊙Sphere (S m)))
    =⟨ ! $ ⊙Susp-⊙Lift (⊙Sphere m) |in-ctx C n ⟩
  C n (⊙Susp (⊙Lift (⊙Sphere m)))
    =⟨ ! (succ-pred n) |in-ctx (λ k → C k (⊙Susp (⊙Lift (⊙Sphere m)))) ⟩
  C (succ (pred n)) (⊙Susp (⊙Lift (⊙Sphere m)))
    =⟨ group-ua (C-Susp (pred n) (⊙Lift (⊙Sphere m))) ⟩
  C (pred n) (⊙Lift (⊙Sphere m))
    =⟨ C-Sphere-≠ (pred n) m (λ p → neq (pred-injective n (ℕ-to-ℤ (S m)) p)) ⟩
  Lift-Unit-group
    ∎

C-Sphere-diag : (m : ℕ) → C (ℕ-to-ℤ m) (⊙Lift (⊙Sphere m)) == C 0 (⊙Lift ⊙S⁰)
C-Sphere-diag O = idp
C-Sphere-diag (S m) =
  C (ℕ-to-ℤ (S m)) (⊙Lift (⊙Sphere (S m)))
    =⟨ ! $ ⊙Susp-⊙Lift (⊙Sphere m) |in-ctx C (ℕ-to-ℤ (S m)) ⟩
  C (ℕ-to-ℤ (S m)) (⊙Susp (⊙Lift (⊙Sphere m)))
    =⟨ group-ua (C-Susp (ℕ-to-ℤ m) (⊙Lift (⊙Sphere m))) ⟩
  C (ℕ-to-ℤ m) (⊙Lift (⊙Sphere m))
    =⟨ C-Sphere-diag m ⟩
  C 0 (⊙Lift ⊙S⁰)
    ∎
