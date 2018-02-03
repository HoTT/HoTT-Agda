{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.ChainComplex
open import cohomology.Theory
open import groups.KernelImage
open import cw.CW

module cw.cohomology.reconstructed.cochain.FirstGroup {i : ULevel} (OT : OrdinaryTheory i) where

  open OrdinaryTheory OT
  open import cw.cohomology.WedgeOfCells OT
  import cw.cohomology.reconstructed.TipCoboundary OT as TC
  import cw.cohomology.reconstructed.HigherCoboundary OT as HC
  import cw.cohomology.reconstructed.TipAndAugment OT as TAA
  open import cw.cohomology.reconstructed.Descending OT
  import cw.cohomology.reconstructed.FirstGroup OT as FCG
  import cw.cohomology.reconstructed.FirstGroupOnDiag OT as FCGD
  import cw.cohomology.reconstructed.GroupsTooHigh OT as CGTH
  open import cw.cohomology.reconstructed.cochain.Complex OT

  private
    ≤-dec-has-all-paths : {m n : ℕ} → has-all-paths (Dec (m ≤ n))
    ≤-dec-has-all-paths = prop-has-all-paths

  private
    abstract
      first-cohomology-group-descend : ∀ {n} (⊙skel : ⊙Skeleton {i} (3 + n))
        →  cohomology-group (cochain-complex ⊙skel) 1
        == cohomology-group (cochain-complex (⊙cw-init ⊙skel)) 1
      first-cohomology-group-descend {n = O} ⊙skel
        = ap2 (λ δ₁ δ₂ → Ker/Im δ₂ δ₁ (CXₙ/Xₙ₋₁-is-abelian (⊙cw-take (lteSR lteS) ⊙skel) 1))
            (coboundary-first-template-descend-from-far {n = 2} ⊙skel (ltSR ltS) ltS)
            (coboundary-higher-template-descend-from-one-above ⊙skel)
      first-cohomology-group-descend {n = S n} ⊙skel -- n = S n
        = ap2 (λ δ₁ δ₂ → Ker/Im δ₂ δ₁ (CXₙ/Xₙ₋₁-is-abelian (⊙cw-take (≤-+-l 1 (lteSR $ lteSR $ inr (O<S n))) ⊙skel) 1))
            (coboundary-first-template-descend-from-far  {n = 3 + n} ⊙skel (ltSR (ltSR (O<S n))) (<-+-l 1 (ltSR (O<S n))))
            (coboundary-higher-template-descend-from-far {n = 3 + n} ⊙skel (<-+-l 1 (ltSR (O<S n))) (<-+-l 2 (O<S n)))

      first-cohomology-group-β : ∀ (⊙skel : ⊙Skeleton {i} 2)
        →  cohomology-group (cochain-complex ⊙skel) 1
        == Ker/Im
            (HC.cw-co∂-last ⊙skel)
            (TC.cw-co∂-head (⊙cw-init ⊙skel))
            (CXₙ/Xₙ₋₁-is-abelian (⊙cw-init ⊙skel) 1)
      first-cohomology-group-β ⊙skel
        = ap2 (λ δ₁ δ₂ → Ker/Im δ₂ δ₁ (CXₙ/Xₙ₋₁-is-abelian (⊙cw-init ⊙skel) 1))
            ( coboundary-first-template-descend-from-two ⊙skel
            ∙ coboundary-first-template-β (⊙cw-init ⊙skel))
            (coboundary-higher-template-β ⊙skel)

      first-cohomology-group-β-one-below : ∀ (⊙skel : ⊙Skeleton {i} 1)
        →  cohomology-group (cochain-complex ⊙skel) 1
        == Ker/Im
            (cst-hom {H = Lift-group {j = i} Unit-group})
            (TC.cw-co∂-head ⊙skel)
            (CXₙ/Xₙ₋₁-is-abelian ⊙skel 1)
      first-cohomology-group-β-one-below ⊙skel
        = ap
            (λ δ₁ → Ker/Im
              (cst-hom {H = Lift-group {j = i} Unit-group})
              δ₁ (CXₙ/Xₙ₋₁-is-abelian ⊙skel 1))
            (coboundary-first-template-β ⊙skel)

  abstract
    first-cohomology-group : ∀ {n} (⊙skel : ⊙Skeleton {i} n)
      → ⊙has-cells-with-choice 0 ⊙skel i
      → C 1 ⊙⟦ ⊙skel ⟧ ≃ᴳ cohomology-group (cochain-complex ⊙skel) 1
    first-cohomology-group {n = 0} ⊙skel ac =
      CGTH.C-cw-iso-ker/im 1 ltS (TAA.C2×CX₀ ⊙skel 0) ⊙skel ac
    first-cohomology-group {n = 1} ⊙skel ac =
          coe!ᴳ-iso (first-cohomology-group-β-one-below ⊙skel)
      ∘eᴳ FCGD.C-cw-iso-ker/im ⊙skel ac
    first-cohomology-group {n = 2} ⊙skel ac =
          coe!ᴳ-iso (first-cohomology-group-β ⊙skel)
      ∘eᴳ FCG.C-cw-iso-ker/im ⊙skel ac
    first-cohomology-group {n = S (S (S n))} ⊙skel ac =
          coe!ᴳ-iso (first-cohomology-group-descend ⊙skel)
      ∘eᴳ first-cohomology-group (⊙cw-init ⊙skel) (⊙init-has-cells-with-choice ⊙skel ac)
      ∘eᴳ C-cw-descend-at-lower ⊙skel (<-+-l 1 (O<S n)) ac
