{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.Theory

module cohomology.Sphere {i} (OT : OrdinaryTheory i) where

open OrdinaryTheory OT

C-Sphere-≠ : (n : ℤ) (m : ℕ) → (n ≠ ℕ-to-ℤ m)
  → C n (⊙Lift (⊙Sphere m)) ≃ᴳ 0ᴳ
C-Sphere-≠ n O neq = C-dimension n neq
C-Sphere-≠ n (S m) neq =
  C n (⊙Lift (⊙Sphere (S m)))
    ≃ᴳ⟨ C-emap n $ ⊙Susp-Lift-econv (⊙Sphere m) ⟩
  C n (⊙Susp (⊙Lift (⊙Sphere m)))
    ≃ᴳ⟨ transportᴳ-equiv (λ n → C n (⊙Susp (⊙Lift (⊙Sphere m)))) (succ-pred n) ⁻¹ᴳ ⟩
  C (succ (pred n)) (⊙Susp (⊙Lift (⊙Sphere m)))
    ≃ᴳ⟨ C-Susp (pred n) (⊙Lift (⊙Sphere m)) ⟩
  C (pred n) (⊙Lift (⊙Sphere m))
    ≃ᴳ⟨ C-Sphere-≠ (pred n) m (λ p → neq (pred-inj n (ℕ-to-ℤ (S m)) p)) ⟩
  0ᴳ
    ≃ᴳ∎

C-Sphere-diag : (m : ℕ) → C (ℕ-to-ℤ m) (⊙Lift (⊙Sphere m)) ≃ᴳ C 0 (⊙Lift ⊙S⁰)
C-Sphere-diag O = idiso _
C-Sphere-diag (S m) =
  C (ℕ-to-ℤ (S m)) (⊙Lift (⊙Sphere (S m)))
    ≃ᴳ⟨ C-emap (ℕ-to-ℤ (S m)) (⊙Susp-Lift-econv (⊙Sphere m)) ⟩
  C (ℕ-to-ℤ (S m)) (⊙Susp (⊙Lift (⊙Sphere m)))
    ≃ᴳ⟨ C-Susp (ℕ-to-ℤ m) (⊙Lift (⊙Sphere m)) ⟩
  C (ℕ-to-ℤ m) (⊙Lift (⊙Sphere m))
    ≃ᴳ⟨ C-Sphere-diag m ⟩
  C 0 (⊙Lift ⊙S⁰)
    ≃ᴳ∎
