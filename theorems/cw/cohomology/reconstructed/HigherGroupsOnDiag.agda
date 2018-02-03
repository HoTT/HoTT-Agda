{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory
open import groups.ExactSequence
open import groups.Exactness
open import groups.HomSequence
open import groups.KernelImageUniqueFactorization
import cw.cohomology.grid.PtdMap as GPM

open import cw.CW

module cw.cohomology.reconstructed.HigherGroupsOnDiag {i} (OT : OrdinaryTheory i)
  {n} (⊙skel : ⊙Skeleton {i} (S (S n))) (ac : ⊙has-cells-with-choice 0 ⊙skel i) where

open OrdinaryTheory OT
open import cw.cohomology.WedgeOfCells OT
open import cw.cohomology.reconstructed.Descending OT

private
  n≤SSn : n ≤ S (S n)
  n≤SSn = lteSR lteS

  ⊙skel₋₁ = ⊙cw-init ⊙skel
  ac₋₁ = ⊙init-has-cells-with-choice ⊙skel ac

  ⊙skel₋₂ = ⊙cw-take n≤SSn ⊙skel
  ac₋₂ = ⊙take-has-cells-with-choice n≤SSn ⊙skel ac

open import cw.cohomology.reconstructed.HigherCoboundary OT ⊙skel
open import cw.cohomology.reconstructed.HigherCoboundaryGrid OT ⊙skel ac

{-

   Coker ≃ C(X₂/X₀) ≃ C(X)
              ^
              |
              |
           C(X₁/X₀)
             WoC

    WoC := Wedges of Cells
-}

private

  C-apex : Group i
  C-apex = C (ℕ-to-ℤ (S (S n))) (⊙Cofiber (⊙cw-incl-tail n≤SSn ⊙skel))

  open import cohomology.LongExactSequence cohomology-theory
    (ℕ-to-ℤ (S n)) (⊙cw-incl-tail n≤SSn ⊙skel)

  C-apex-iso-C-cw : C-apex ≃ᴳ C (ℕ-to-ℤ (S (S n))) ⊙⟦ ⊙skel ⟧
  C-apex-iso-C-cw = Exact2.G-trivial-and-L-trivial-implies-H-iso-K
    (exact-seq-index 1 C-cofiber-exact-seq)
    (exact-seq-index 2 C-cofiber-exact-seq)
    (C-cw-at-higher ⊙skel₋₂ ltS ac₋₂)
    (C-cw-at-higher ⊙skel₋₂ (ltSR ltS) ac₋₂)

open import groups.KernelImage (cst-hom {H = Lift-group {j = i} Unit-group}) cw-co∂-last
  (CXₙ/Xₙ₋₁-is-abelian ⊙skel (ℕ-to-ℤ (S (S n))))
open import groups.KernelCstImage (Lift-group {j = i} Unit-group) cw-co∂-last
  (CXₙ/Xₙ₋₁-is-abelian ⊙skel (ℕ-to-ℤ (S (S n))))

C-cw-iso-ker/im : C (ℕ-to-ℤ (S (S n))) ⊙⟦ ⊙skel ⟧ ≃ᴳ Ker/Im
C-cw-iso-ker/im = (C-apex-iso-C-cw ∘eᴳ Coker-cw-co∂-last ∘eᴳ Ker-cst-quot-Im) ⁻¹ᴳ
