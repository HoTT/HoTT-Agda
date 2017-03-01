{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory

open import cw.CW

module cw.cohomology.ZerothCohomologyGroupOnDiag {i} (OT : OrdinaryTheory i)
  (⊙skel : ⊙Skeleton {i} 0) (ac : ⊙has-cells-with-choice 0 ⊙skel i) where

open OrdinaryTheory OT
open import cw.cohomology.TipAndAugment OT ⊙skel

open import groups.KernelSndImageInl G {H = CX₀}
  {K = Lift-group {j = i} Unit-group}
  cst-hom cst-hom (λ _ → idp)
  G×CX₀-is-abelian

open import groups.KernelImage
  (cst-hom {G = G×CX₀} {H = Lift-group {j = i} Unit-group})
  cw-coε G×CX₀-is-abelian

C-cw-iso-ker/im : C 0 ⊙⟦ ⊙skel ⟧ ≃ᴳ Ker/Im
C-cw-iso-ker/im =
      Ker-φ-snd-quot-Im-inl
  ∘eᴳ full-subgroup (ker-cst-hom-is-full CX₀ (Lift-group {j = i} Unit-group)) ⁻¹ᴳ
