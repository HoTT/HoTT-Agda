{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory

module cohomology.Coproduct {i} (CT : CohomologyTheory i)
  (n : ℤ) (X Y : Ptd i) where

open CohomologyTheory CT
open import cohomology.Sigma CT

private
  P : Bool → Ptd i
  P true = X
  P false = Y

C-⊔ : C n (X ⊙⊔ Y) ≃ᴳ C n (X ⊙∨ Y) ×ᴳ C2 n
C-⊔ = (×ᴳ-emap
        (C-emap n (≃-to-⊙≃ ( BigWedge-Bool-equiv-Wedge P
                          ∘e BigWedge-emap-l P lower-equiv) idp))
        (idiso _)) ⁻¹ᴳ
  ∘eᴳ C-Σ n (⊙Lift {j = i} ⊙Bool) (P ∘ lower)
  ∘eᴳ C-emap n (≃-to-⊙≃ ( ΣBool-equiv-⊔ (de⊙ ∘ P)
                       ∘e Σ-emap-l (de⊙ ∘ P) lower-equiv) idp)
