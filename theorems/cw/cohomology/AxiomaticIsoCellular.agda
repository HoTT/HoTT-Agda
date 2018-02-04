{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cw.CW
open import cw.FinCW
open import cw.FinBoundary
open import cohomology.ChainComplex
open import cohomology.Theory

module cw.cohomology.AxiomaticIsoCellular (OT : OrdinaryTheory lzero) where

  open OrdinaryTheory OT
  open import cw.cohomology.cellular.ChainComplex
  import cw.cohomology.reconstructed.cochain.Complex OT as RCC
  open import cw.cohomology.ReconstructedCohomologyGroups OT
  open import cw.cohomology.ReconstructedCochainsEquivCellularCochains OT

  axiomatic-iso-cellular : ∀ m {n} (⊙fin-skel : ⊙FinSkeleton n)
    →  C m ⊙⟦ ⊙⦉ ⊙fin-skel ⦊ ⟧
    ≃ᴳ cohomology-group
        (cochain-complex ⦉ ⊙FinSkeleton.skel ⊙fin-skel ⦊
          (FinSkeleton-has-cells-with-dec-eq (⊙FinSkeleton.skel ⊙fin-skel))
          (FinSkeleton-has-degrees-with-finite-support (⊙FinSkeleton.skel ⊙fin-skel))
          (C2-abgroup 0))
        m
  axiomatic-iso-cellular m ⊙fin-skel =
      C m ⊙⟦ ⊙⦉ ⊙fin-skel ⦊ ⟧
        ≃ᴳ⟨ reconstructed-cohomology-group m ⊙⦉ ⊙fin-skel ⦊
              (⊙FinSkeleton-has-cells-with-choice 0 ⊙fin-skel lzero) ⟩
      cohomology-group (RCC.cochain-complex ⊙⦉ ⊙fin-skel ⦊) m
        ≃ᴳ⟨ frc-iso-fcc ⊙fin-skel m ⟩
      cohomology-group
        (cochain-complex ⦉ ⊙FinSkeleton.skel ⊙fin-skel ⦊
          (FinSkeleton-has-cells-with-dec-eq (⊙FinSkeleton.skel ⊙fin-skel))
          (FinSkeleton-has-degrees-with-finite-support (⊙FinSkeleton.skel ⊙fin-skel))
          (C2-abgroup 0))
        m
        ≃ᴳ∎
