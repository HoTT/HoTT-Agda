{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory

open import cw.CW

module cw.cohomology.reconstructed.ZerothGroupOnDiag {i} (OT : OrdinaryTheory i)
  (⊙skel : ⊙Skeleton {i} 0) (ac : ⊙has-cells-with-choice 0 ⊙skel i) where

open OrdinaryTheory OT
open import cw.cohomology.reconstructed.TipAndAugment OT ⊙skel

open import groups.KernelSndImageInl (C2 0) {H = CX₀ 0}
  {K = Lift-group {j = i} Unit-group}
  cst-hom cst-hom (λ _ → idp)
  (C2×CX₀-is-abelian 0)

open import groups.KernelImage
  (cst-hom {G = C2×CX₀ 0} {H = Lift-group {j = i} Unit-group})
  cw-coε (C2×CX₀-is-abelian 0)

C-cw-iso-ker/im : C 0 ⊙⟦ ⊙skel ⟧ ≃ᴳ Ker/Im
C-cw-iso-ker/im =
      Ker-φ-snd-quot-Im-inl
  ∘eᴳ full-subgroup (ker-cst-hom-is-full (CX₀ 0) (Lift-group {j = i} Unit-group)) ⁻¹ᴳ
