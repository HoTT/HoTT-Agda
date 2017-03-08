{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory

module cohomology.Coproduct {i} (CT : CohomologyTheory i)
  (n : ℤ) (X Y : Ptd i) where

open CohomologyTheory CT

private
  P : Bool → Ptd i
  P true = X
  P false = Y

import cohomology.Sigma CT n (⊙Lift {j = i} ⊙Bool) (P ∘ lower) as CΣ

iso : C n (X ⊙⊔ Y) ≃ᴳ C n (X ⊙∨ Y) ×ᴳ C2 n
iso = (×ᴳ-emap
        (C-emap n (≃-to-⊙≃ ( BigWedge-Bool-equiv-Wedge P
                          ∘e BigWedge-emap-l P lower-equiv) idp))
        (idiso _)) ⁻¹ᴳ
  ∘eᴳ CΣ.iso
  ∘eᴳ C-emap n (≃-to-⊙≃ ( ΣBool-equiv-⊔ (de⊙ ∘ P)
                       ∘e Σ-emap-l (de⊙ ∘ P) lower-equiv) idp)

