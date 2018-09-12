{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cw.CW
open import homotopy.DisjointlyPointedSet
open import groups.Int
open import cohomology.Theory
open import cohomology.ChainComplex

module cw.cohomology.ReconstructedCochainsIsoCellularCochains {i : ULevel}
  (OT : OrdinaryTheory i) where

  open FreeAbelianGroup

  open OrdinaryTheory OT
  open import cw.cohomology.WedgeOfCells OT
  open import cw.cohomology.cellular.ChainComplex as CCC
  open import cw.cohomology.reconstructed.cochain.Complex OT as RCC
  open import cw.cohomology.reconstructed.TipAndAugment OT

  private
    rcc-iso-ccc-nth : ∀ {n} (⊙skel : ⊙Skeleton n) {m} (m≤n : m ≤ n)
      → ⊙has-cells-with-choice 0 ⊙skel i
      →  AbGroup.grp (RCC.cochain-template ⊙skel (inl m≤n))
      ≃ᴳ hom-group (AbGroup.grp (CCC.chain-template (⊙Skeleton.skel ⊙skel) (inl m≤n))) (C2-abgroup 0)
    rcc-iso-ccc-nth ⊙skel {m = O} (inl idp) ac
      =   Freeness.extend-iso _ (C2-abgroup 0)
      ∘eᴳ C2×CX₀-diag-β ⊙skel ac
    rcc-iso-ccc-nth ⊙skel {m = S m} (inl idp) ac
      =   Freeness.extend-iso _ (C2-abgroup 0)
      ∘eᴳ CXₙ/Xₙ₋₁-diag-β ⊙skel ac
    rcc-iso-ccc-nth ⊙skel {m = O} (inr ltS) ac =
      rcc-iso-ccc-nth (⊙cw-init ⊙skel) (inl idp) (⊙init-has-cells-with-choice ⊙skel ac)
    rcc-iso-ccc-nth ⊙skel {m = S m} (inr ltS) ac =
      rcc-iso-ccc-nth (⊙cw-init ⊙skel) (inl idp) (⊙init-has-cells-with-choice ⊙skel ac)
    rcc-iso-ccc-nth ⊙skel {m = O} (inr (ltSR lt)) ac =
      rcc-iso-ccc-nth (⊙cw-init ⊙skel) (inr lt) (⊙init-has-cells-with-choice ⊙skel ac)
    rcc-iso-ccc-nth ⊙skel {m = S m} (inr (ltSR lt)) ac =
      rcc-iso-ccc-nth (⊙cw-init ⊙skel) (inr lt) (⊙init-has-cells-with-choice ⊙skel ac)

    rcc-iso-ccc-above : ∀ {n} (⊙skel : ⊙Skeleton n) {m} (m≰n : ¬ (m ≤ n))
      →  AbGroup.grp (RCC.cochain-template ⊙skel (inr m≰n))
      ≃ᴳ hom-group (AbGroup.grp (CCC.chain-template (⊙Skeleton.skel ⊙skel) (inr m≰n))) (C2-abgroup 0)
    rcc-iso-ccc-above ⊙skel _
      =   pre∘ᴳ-iso (C2-abgroup 0) lower-iso
      ∘eᴳ trivial-iso-Unit (hom₁-Unit-is-trivial (C2-abgroup 0)) ⁻¹ᴳ
      ∘eᴳ lower-iso

  rcc-iso-ccc-template : ∀ {n} (⊙skel : ⊙Skeleton n) {m : ℕ} (m≤n? : Dec (m ≤ n))
    → ⊙has-cells-with-choice 0 ⊙skel i
    →  AbGroup.grp (RCC.cochain-template ⊙skel m≤n?)
    ≃ᴳ hom-group (AbGroup.grp (CCC.chain-template (⊙Skeleton.skel ⊙skel) m≤n?)) (C2-abgroup 0)
  rcc-iso-ccc-template ⊙skel {m} (inl m≤n) ac = rcc-iso-ccc-nth ⊙skel m≤n ac
  rcc-iso-ccc-template ⊙skel {m} (inr m≰n) _ = rcc-iso-ccc-above ⊙skel m≰n

  rcc-iso-ccc : ∀ {n} (⊙skel : ⊙Skeleton n) (m : ℕ)
    → ⊙has-cells-with-choice 0 ⊙skel i
    →  AbGroup.grp (RCC.cochain-template ⊙skel (≤-dec m n))
    ≃ᴳ hom-group (AbGroup.grp (CCC.chain-template (⊙Skeleton.skel ⊙skel) (≤-dec m n))) (C2-abgroup 0)
  rcc-iso-ccc {n} ⊙skel m = rcc-iso-ccc-template ⊙skel (≤-dec m n)

  rhead-iso-chead : C2 0 ≃ᴳ hom-group (Lift-group {j = i} ℤ-group) (C2-abgroup 0)
  rhead-iso-chead
    =   pre∘ᴳ-iso (C2-abgroup 0) (lower-iso {j = i})
    ∘eᴳ ℤ→ᴳ-iso-idf (C2-abgroup 0) ⁻¹ᴳ
