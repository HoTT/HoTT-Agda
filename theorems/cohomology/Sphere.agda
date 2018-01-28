{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory

module cohomology.Sphere {i} (OT : OrdinaryTheory i) where

open OrdinaryTheory OT

abstract
  C-Sphere-≠-is-trivial : (n : ℤ) (m : ℕ) → (n ≠ ℕ-to-ℤ m)
    → is-trivialᴳ (C n (⊙Lift (⊙Sphere m)))
  C-Sphere-≠-is-trivial n O n≠0 = C-dimension n≠0
  C-Sphere-≠-is-trivial n (S m) n≠Sm = iso-preserves'-trivial
    (C n (⊙Lift (⊙Sphere (S m)))
      ≃ᴳ⟨ C-emap n $ ⊙Susp-Lift-econv (⊙Sphere m) ⟩
    C n (⊙Susp (⊙Lift (⊙Sphere m)))
      ≃ᴳ⟨ transportᴳ-iso (λ n → C n (⊙Susp (⊙Lift (⊙Sphere m)))) (succ-pred n) ⁻¹ᴳ ⟩
    C (succ (pred n)) (⊙Susp (⊙Lift (⊙Sphere m)))
      ≃ᴳ⟨ C-Susp (pred n) (⊙Lift (⊙Sphere m)) ⟩
    C (pred n) (⊙Lift (⊙Sphere m))
      ≃ᴳ∎)
    (C-Sphere-≠-is-trivial (pred n) m (pred-≠ n≠Sm))

C-Sphere-diag : (m : ℕ) → C (ℕ-to-ℤ m) (⊙Lift (⊙Sphere m)) ≃ᴳ C2 0
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
