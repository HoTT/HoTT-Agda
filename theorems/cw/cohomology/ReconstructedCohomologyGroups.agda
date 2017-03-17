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
  open import cw.cohomology.ReconstructedZerothCohomologyGroup OT
  open import cw.cohomology.ReconstructedFirstCohomologyGroup OT
  open import cw.cohomology.ReconstructedHigherCohomologyGroups OT

  abstract
    reconstructed-group : ∀ m {n} (⊙skel : ⊙Skeleton {i} n)
      → ⊙has-cells-with-choice 0 ⊙skel i
      → C m ⊙⟦ ⊙skel ⟧ ≃ᴳ cohomology-group (cochain-complex ⊙skel) m
    reconstructed-group (pos 0) ⊙skel ac =
      zeroth-group ⊙skel ac
    reconstructed-group (pos 1) ⊙skel ac =
      first-group ⊙skel ac
    reconstructed-group (pos (S (S m))) ⊙skel ac =
      higher-group m ⊙skel ac
    reconstructed-group (negsucc m) ⊙skel ac =
      lift-iso {j = i} ∘eᴳ trivial-iso-0ᴳ (C-cw-at-negsucc ⊙skel m ac)
