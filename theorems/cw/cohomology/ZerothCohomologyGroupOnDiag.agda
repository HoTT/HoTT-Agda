{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory

open import cw.CW

module cw.cohomology.ZerothCohomologyGroupOnDiag {i} (OT : OrdinaryTheory i)
  (⊙skel : ⊙Skeleton {i} 0) (ac : ⊙has-cells-with-choice 0 ⊙skel i) where

open OrdinaryTheory OT
open import cw.cohomology.TipAndAugment OT ⊙skel

open import groups.PropQuotOfInl G {H = CX₀}
  {K = Lift-group {j = i} Unit-group}
  G×CX₀-is-abelian
  cst-hom cst-hom (λ _ → idp)

C-cw-iso-ker/im : C 0 ⊙⟦ ⊙skel ⟧
  ≃ᴳ QuotGroup (quot-of-sub
      (ker-propᴳ (cst-hom {G = G×CX₀} {H = Lift-group {j = i} Unit-group}))
      (im-npropᴳ cw-coε G×CX₀-is-abelian))
C-cw-iso-ker/im =
      Ker-inl-quot-Im-φ-snd
  ∘eᴳ (full-subgroup (ker-cst-is-full CX₀ (Lift-group {j = i} Unit-group))) ⁻¹ᴳ
