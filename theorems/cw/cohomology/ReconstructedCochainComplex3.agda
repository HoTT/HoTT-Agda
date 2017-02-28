{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.ChainComplex
open import cohomology.Theory
open import cw.CW

module cw.cohomology.ReconstructedCochainComplex3 {i : ULevel} (OT : OrdinaryTheory i) where

  open OrdinaryTheory OT
  import cw.cohomology.CoboundaryGrid OT as CG
  import cw.cohomology.TipAndAugment OT as TAA
  import cw.cohomology.TipGrid OT as TG
  open import cw.cohomology.ReconstructedCochainComplex OT
  open import cw.cohomology.ReconstructedCochainComplex2 OT
  import cw.cohomology.ZerothCohomologyGroup OT as ZCG
  import cw.cohomology.ZerothCohomologyGroupOnDiag OT as ZCGD
  open import cw.cohomology.Descending OT

  abstract
    zeroth-cohomology-group : ∀ {n} (⊙skel : ⊙Skeleton {i} n) ac
      → C 0 ⊙⟦ ⊙skel ⟧ ≃ᴳ cohomology-group (cochain-complex ⊙skel ac) 0
    zeroth-cohomology-group {n = 0} ⊙skel ac = ZCGD.C-cw-iso-ker/im ⊙skel ac
    zeroth-cohomology-group {n = 1} ⊙skel ac =
          coeᴳ-iso (zeroth-cohomology-group-β ⊙skel ac) ⁻¹ᴳ
      ∘eᴳ ZCG.C-cw-iso-ker/im ⊙skel ac
    zeroth-cohomology-group {n = S (S n)} ⊙skel ac =
          coeᴳ-iso (zeroth-cohomology-group-descend ⊙skel ac) ⁻¹ᴳ
      ∘eᴳ zeroth-cohomology-group (⊙cw-init ⊙skel) (⊙init-has-cells-with-choice ⊙skel ac)
      ∘eᴳ C-cw-descend 0 (pos-≠ (ℕ-O≠S n)) (pos-≠ (ℕ-O≠S (S n))) ⊙skel ac
