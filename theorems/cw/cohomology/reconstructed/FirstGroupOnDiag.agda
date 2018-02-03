{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory
open import cohomology.PtdMapSequence
open import groups.ExactSequence
open import groups.Exactness
open import groups.HomSequence

open import cw.CW

module cw.cohomology.reconstructed.FirstGroupOnDiag {i} (OT : OrdinaryTheory i)
  (⊙skel : ⊙Skeleton {i} 1) (ac : ⊙has-cells-with-choice 0 ⊙skel i) where

open OrdinaryTheory OT
open import cw.cohomology.WedgeOfCells OT
open import cw.cohomology.reconstructed.TipCoboundary OT ⊙skel
open import cw.cohomology.reconstructed.TipGrid OT ⊙skel ac

{-
    Coker ≃ C(X₁) = C(X)
              ^
              |
              |
           C(X₁/X₀)
             WoC

    WoC := Wedges of Cells
-}

open import groups.KernelImage {K = Lift-group {j = i} Unit-group} cst-hom cw-co∂-head CX₁/X₀-is-abelian
open import groups.KernelCstImage (Lift-group {j = i} Unit-group) cw-co∂-head CX₁/X₀-is-abelian

C-cw-iso-ker/im : C 1 ⊙⟦ ⊙skel ⟧ ≃ᴳ Ker/Im
C-cw-iso-ker/im = Ker-cst-quot-Im ⁻¹ᴳ ∘eᴳ Coker-cw-co∂-head ⁻¹ᴳ where
