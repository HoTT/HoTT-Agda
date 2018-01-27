{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.Bouquet
open import cohomology.Theory

module cohomology.Bouquet {i} (OT : OrdinaryTheory i) where

open OrdinaryTheory OT
open import cohomology.Sphere OT

C-Bouquet : ∀ n (I : Type i) → has-choice 0 I i
  → C (ℕ-to-ℤ n) (⊙Bouquet I n) ≃ᴳ Πᴳ I (λ _ → C2 0)
C-Bouquet n I I-choice =
  C (ℕ-to-ℤ n) (⊙Bouquet I n)
    ≃ᴳ⟨ C-emap (ℕ-to-ℤ n) (⊙BigWedge-emap-r (λ _ → ⊙lower-equiv)) ⟩
  C (ℕ-to-ℤ n) (⊙BouquetLift I n)
    ≃ᴳ⟨ C-additive-iso (ℕ-to-ℤ n) (BouquetLift-family I n) I-choice ⟩
  Πᴳ I (λ _ → C (ℕ-to-ℤ n) (⊙Lift (⊙Sphere n)))
    ≃ᴳ⟨ Πᴳ-emap-r I (λ _ → C-Sphere-diag n) ⟩
  Πᴳ I (λ _ → C2 0)
    ≃ᴳ∎
