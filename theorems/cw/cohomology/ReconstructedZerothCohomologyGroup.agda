{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.ChainComplex
open import cohomology.Theory
open import groups.KernelImage
open import cw.CW

module cw.cohomology.ReconstructedZerothCohomologyGroup {i : ULevel} (OT : OrdinaryTheory i) where

  open OrdinaryTheory OT
  import cw.cohomology.TipCoboundary OT as TC
  import cw.cohomology.TipAndAugment OT as TAA
  open import cw.cohomology.Descending OT
  open import cw.cohomology.ReconstructedCochainComplex OT
  import cw.cohomology.ZerothCohomologyGroup OT as ZCG
  import cw.cohomology.ZerothCohomologyGroupOnDiag OT as ZCGD

  private
    ≤-dec-has-all-paths : {m n : ℕ} → has-all-paths (Dec (m ≤ n))
    ≤-dec-has-all-paths = prop-has-all-paths (Dec-level ≤-is-prop)

  private
    abstract
      zeroth-cohomology-group-descend : ∀ {n} (⊙skel : ⊙Skeleton {i} (2 + n))
        →  cohomology-group (cochain-complex ⊙skel) 0
        == cohomology-group (cochain-complex (⊙cw-init ⊙skel)) 0
      zeroth-cohomology-group-descend {n = O} ⊙skel
        = ap
            (λ δ → Ker/Im δ
              (TAA.cw-coε (⊙cw-take (lteSR lteS) ⊙skel))
              (TAA.C2×CX₀-is-abelian (⊙cw-take (lteSR lteS) ⊙skel) 0))
            (coboundary-first-template-descend-from-two ⊙skel)
      zeroth-cohomology-group-descend {n = S n} ⊙skel
        = ap (λ δ → Ker/Im δ
                (TAA.cw-coε (⊙cw-take (inr (O<S (2 + n))) ⊙skel))
                (TAA.C2×CX₀-is-abelian (⊙cw-take (inr (O<S (2 + n))) ⊙skel) 0))
            (coboundary-first-template-descend-from-far ⊙skel (O<S (1 + n)) (<-+-l 1 (O<S n)))

      zeroth-cohomology-group-β : ∀ (⊙skel : ⊙Skeleton {i} 1)
        →  cohomology-group (cochain-complex ⊙skel) 0
        == Ker/Im
            (TC.cw-co∂-head ⊙skel)
            (TAA.cw-coε (⊙cw-init ⊙skel))
            (TAA.C2×CX₀-is-abelian (⊙cw-init ⊙skel) 0)
      zeroth-cohomology-group-β ⊙skel
        = ap
            (λ δ → Ker/Im δ
              (TAA.cw-coε (⊙cw-init ⊙skel))
              (TAA.C2×CX₀-is-abelian (⊙cw-init ⊙skel) 0))
            (coboundary-first-template-β ⊙skel)

  abstract
    zeroth-cohomology-group : ∀ {n} (⊙skel : ⊙Skeleton {i} n)
      → ⊙has-cells-with-choice 0 ⊙skel i
      → C 0 ⊙⟦ ⊙skel ⟧ ≃ᴳ cohomology-group (cochain-complex ⊙skel) 0
    zeroth-cohomology-group {n = 0} ⊙skel ac = ZCGD.C-cw-iso-ker/im ⊙skel ac
    zeroth-cohomology-group {n = 1} ⊙skel ac =
          coe!ᴳ-iso (zeroth-cohomology-group-β ⊙skel)
      ∘eᴳ ZCG.C-cw-iso-ker/im ⊙skel ac
    zeroth-cohomology-group {n = S (S n)} ⊙skel ac =
          coe!ᴳ-iso (zeroth-cohomology-group-descend ⊙skel)
      ∘eᴳ zeroth-cohomology-group (⊙cw-init ⊙skel) (⊙init-has-cells-with-choice ⊙skel ac)
      ∘eᴳ C-cw-descend-at-lower ⊙skel (O<S n) ac
