{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cw.CW
open import homotopy.DisjointlyPointedSet
open import cohomology.Theory
open import cohomology.ChainComplex

module cw.cohomology.ReconstructedCochainsIsoCellularCochains {i : ULevel}
  (OT : OrdinaryTheory i) where

  open OrdinaryTheory OT
  open import cw.cohomology.CellularChainComplex as CCC
  open import cw.cohomology.ReconstructedCochainComplex OT as RCC
  open import cw.cohomology.TipAndAugment OT
  open import cw.cohomology.WedgeOfCells OT

  private
    rcc-iso-ccc-nth : ∀ {n} (⊙skel : ⊙Skeleton n) {m} (m≤n : m ≤ n)
      → ⊙has-cells-with-choice 0 ⊙skel i
      →  AbGroup.grp (RCC.cochain-template ⊙skel (inl m≤n))
      ≃ᴳ hom-group (AbGroup.grp (CCC.chain-template (⊙Skeleton.skel ⊙skel) (inl m≤n))) (C2-abgroup 0)
    rcc-iso-ccc-nth ⊙skel {m = O} (inl idp) ac
      =   FreeAbGroup-extend-iso (C2-abgroup 0)
      ∘eᴳ Πᴳ-emap-l (λ _ → C2 0) (separable-unite-equiv (⊙Skeleton.pt-dec ⊙skel))
      ∘eᴳ Πᴳ₁-⊔-iso-×ᴳ {A = Unit} {B = MinusPoint (⊙cw-head ⊙skel)} (λ _ → C2 0) ⁻¹ᴳ
      ∘eᴳ ×ᴳ-emap (Πᴳ₁-Unit ⁻¹ᴳ) (CX₀-β ⊙skel 0 ac)
    rcc-iso-ccc-nth ⊙skel {m = S m} (inl idp) ac
      =   FreeAbGroup-extend-iso (C2-abgroup 0)
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

  rcc-iso-ccc : ∀ {n} (⊙skel : ⊙Skeleton n) (m : ℕ)
    → ⊙has-cells-with-choice 0 ⊙skel i
    →  AbGroup.grp (RCC.cochain-template ⊙skel (≤-dec m n))
    ≃ᴳ hom-group (AbGroup.grp (CCC.chain-template (⊙Skeleton.skel ⊙skel) (≤-dec m n))) (C2-abgroup 0)
  rcc-iso-ccc {n} ⊙skel m ac with ≤-dec m n
  rcc-iso-ccc ⊙skel m ac | inl m≤n = rcc-iso-ccc-nth ⊙skel m≤n ac
  rcc-iso-ccc ⊙skel m ac | inr m≰n = rcc-iso-ccc-above ⊙skel m≰n

  rhead-iso-chead : C2 0 ≃ᴳ hom-group ℤ-group (C2-abgroup 0)
  rhead-iso-chead
    =   pre∘ᴳ-iso (C2-abgroup 0) ℤ-iso-FreeAbGroup-Unit
    ∘eᴳ FreeAbGroup-extend-iso (C2-abgroup 0)
    ∘eᴳ Πᴳ₁-Unit ⁻¹ᴳ
