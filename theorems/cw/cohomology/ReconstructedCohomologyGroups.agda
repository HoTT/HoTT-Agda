{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.ChainComplex
open import cohomology.Theory
open import groups.KernelImage
open import cw.CW

module cw.cohomology.ReconstructedCohomologyGroups {i : ULevel} (OT : OrdinaryTheory i) where

  open OrdinaryTheory OT
  open import cw.cohomology.Descending OT
  open import cw.cohomology.ReconstructedCochainComplex OT
  open import cw.cohomology.ZerothReconstructedCohomologyGroup OT
  open import cw.cohomology.FirstReconstructedCohomologyGroup OT
  open import cw.cohomology.HigherReconstructedCohomologyGroups OT

  abstract
    reconstructed-cohomology-group : ∀ m {n} (⊙skel : ⊙Skeleton {i} n)
      → ⊙has-cells-with-choice 0 ⊙skel i
      → C m ⊙⟦ ⊙skel ⟧ ≃ᴳ cohomology-group (cochain-complex ⊙skel) m
    reconstructed-cohomology-group (pos 0) ⊙skel ac =
      zeroth-cohomology-group ⊙skel ac
    reconstructed-cohomology-group (pos 1) ⊙skel ac =
      first-cohomology-group ⊙skel ac
    reconstructed-cohomology-group (pos (S (S m))) ⊙skel ac =
      higher-cohomology-group m ⊙skel ac
    reconstructed-cohomology-group (negsucc m) ⊙skel ac =
      lift-iso {j = i} ∘eᴳ trivial-iso-0ᴳ (C-cw-at-negsucc m ⊙skel ac)
