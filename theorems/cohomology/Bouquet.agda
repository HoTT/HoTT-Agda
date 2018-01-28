{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.Bouquet
open import cohomology.Theory

module cohomology.Bouquet {i} (OT : OrdinaryTheory i) where

open OrdinaryTheory OT
open import cohomology.Sphere OT

C-Bouquet-diag : ∀ n (I : Type i) → has-choice 0 I i
  → C (ℕ-to-ℤ n) (⊙Bouquet I n) ≃ᴳ Πᴳ I (λ _ → C2 0)
C-Bouquet-diag n I I-choice =
  C (ℕ-to-ℤ n) (⊙Bouquet I n)
    ≃ᴳ⟨ C-emap (ℕ-to-ℤ n) (⊙BigWedge-emap-r (λ _ → ⊙lower-equiv)) ⟩
  C (ℕ-to-ℤ n) (⊙BouquetLift I n)
    ≃ᴳ⟨ C-additive-iso (ℕ-to-ℤ n) (BouquetLift-family I n) I-choice ⟩
  Πᴳ I (λ _ → C (ℕ-to-ℤ n) (⊙Lift (⊙Sphere n)))
    ≃ᴳ⟨ Πᴳ-emap-r I (λ _ → C-Sphere-diag n) ⟩
  Πᴳ I (λ _ → C2 0)
    ≃ᴳ∎

abstract
  C-Bouquet-≠-is-trivial : ∀ (n : ℤ) (I : Type i) (m : ℕ)
    → (n ≠ ℕ-to-ℤ m) → has-choice 0 I i
    → is-trivialᴳ (C n (⊙Bouquet I m))
  C-Bouquet-≠-is-trivial n I m n≠m I-choice = iso-preserves'-trivial
    (C n (⊙Bouquet I m)
      ≃ᴳ⟨ C-emap n (⊙BigWedge-emap-r (λ _ → ⊙lower-equiv)) ⟩
    C n (⊙BouquetLift I m)
      ≃ᴳ⟨ C-additive-iso n (BouquetLift-family I m) I-choice ⟩
    Πᴳ I (λ _ → C n (⊙Lift (⊙Sphere m)))
      ≃ᴳ∎)
    (Πᴳ-is-trivial I (λ _ → C n (⊙Lift (⊙Sphere m))) (λ _ → C-Sphere-≠-is-trivial n m n≠m))
