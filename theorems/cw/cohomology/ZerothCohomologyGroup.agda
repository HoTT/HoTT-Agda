{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import groups.Cokernel
open import cohomology.Theory

open import cw.CW

module cw.cohomology.ZerothCohomologyGroup {i} (OT : OrdinaryTheory i)
  (⊙skel : ⊙Skeleton {i} 1) (ac : ⊙has-cells-with-choice 0 ⊙skel i) where

open OrdinaryTheory OT
open import cw.cohomology.TipCoboundary OT ⊙skel
open import cw.cohomology.TipAndAugment OT (⊙cw-init ⊙skel)
open import cw.cohomology.TipGrid OT ⊙skel ac

{-

    C(X₀)<------C(X₁) = C(X)
                  ^
                  |
                  |
               C(X₁/X₀)
                 WoC

    WoC := Wedges of Cells
-}

open import groups.KernelSndImageInl (C2 0) {H = CX₀ 0}
  {K = C 1 (⊙Cofiber (⊙cw-incl-last ⊙skel))}
  cw-co∂-head' cw-co∂-head (λ _ → idp)
  (C2×CX₀-is-abelian 0)

module CokerCoε = Coker cw-coε (C2×CX₀-is-abelian 0)

open import groups.KernelImage cw-co∂-head cw-coε (C2×CX₀-is-abelian 0)

C-cw-iso-ker/im : C 0 ⊙⟦ ⊙skel ⟧ ≃ᴳ Ker/Im
C-cw-iso-ker/im = Ker-φ-snd-quot-Im-inl ∘eᴳ Ker-cw-co∂-head'
