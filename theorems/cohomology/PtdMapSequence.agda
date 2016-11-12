{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.PtdMapSequence
open import groups.HomSequence
open import cohomology.Theory

module cohomology.PtdMapSequence {i} (CT : CohomologyTheory i) where

  open CohomologyTheory CT
  open import cohomology.BaseIndependence CT

  -- FIXME maybe this should be named [ap-C-seq],
  -- but I do not know how to name [C-seq-isemap]. -favonia

  C-seq : ∀ {X Y : Ptd i} (n : ℤ)
    → PtdMapSequence X Y
    → HomSequence (C n Y) (C n X)
  C-seq n (X ⊙⊣|) = C n X ⊣|ᴳ
  C-seq n (X ⊙→⟨ f ⟩ seq) = HomSeq-snoc (C-seq n seq) (C-fmap n f)

  C-comm-square : ∀ (n : ℤ) {X₀ X₁ Y₀ Y₁ : Ptd i}
    → {f₀ : X₀ ⊙→ Y₀} {f₁ : X₁ ⊙→ Y₁} {hX : X₀ ⊙→ X₁} {hY : Y₀ ⊙→ Y₁}
    → CommSquare (fst f₀) (fst f₁) (fst hX) (fst hY)
    → CommSquareᴳ (C-fmap n f₁) (C-fmap n f₀) (C-fmap n hY) (C-fmap n hX)
  C-comm-square n {f₀ = f₀} {f₁} {hX} {hY} (comm-sqr □) = comm-sqrᴳ λ y₁ →
    ∘-CEl-fmap n hX f₁ y₁ ∙ CEl-fmap-base-indep' n (λ x → ! (□ x)) y₁ ∙ CEl-fmap-∘ n hY f₀ y₁

  C-seq-fmap : ∀ {X₀ X₁ Y₀ Y₁ : Ptd i} (n : ℤ)
    {seq₀ : PtdMapSequence X₀ Y₀} {seq₁ : PtdMapSequence X₁ Y₁}
    {hX : X₀ ⊙→ X₁} {hY : Y₀ ⊙→ Y₁}
    → PtdMapSeqMap seq₀ seq₁ hX hY
    → HomSeqMap (C-seq n seq₁) (C-seq n seq₀) (C-fmap n hY) (C-fmap n hX)
  C-seq-fmap n (hX ⊙↓|) = C-fmap n hX ↓|ᴳ
  C-seq-fmap n (hX ⊙↓⟨ □ ⟩ seq) = HomSeqMap-snoc (C-seq-fmap n seq) (C-comm-square n □)

  C-seq-isemap : ∀ {X₀ X₁ Y₀ Y₁ : Ptd i} (n : ℤ)
    {seq₀ : PtdMapSequence X₀ Y₀} {seq₁ : PtdMapSequence X₁ Y₁}
    {hX : X₀ ⊙→ X₁} {hY : Y₀ ⊙→ Y₁}
    {seq-map : PtdMapSeqMap seq₀ seq₁ hX hY}
    → is-⊙seq-equiv seq-map
    → is-seqᴳ-equiv (C-seq-fmap n seq-map)
  C-seq-isemap n {seq-map = h ⊙↓|} h-is-equiv = CEl-isemap n h h-is-equiv
  C-seq-isemap n {seq-map = h ⊙↓⟨ □ ⟩ seq} (h-is-equiv , seq-is-equiv) =
    is-seqᴳ-equiv-snoc (C-seq-isemap n seq-is-equiv) (CEl-isemap n h h-is-equiv)

  C-seq-emap : ∀ {X₀ X₁ Y₀ Y₁ : Ptd i} (n : ℤ)
    {seq₀ : PtdMapSequence X₀ Y₀} {seq₁ : PtdMapSequence X₁ Y₁}
    {hX : X₀ ⊙→ X₁} {hY : Y₀ ⊙→ Y₁}
    → PtdMapSeqEquiv seq₀ seq₁ hX hY
    → HomSeqEquiv (C-seq n seq₁) (C-seq n seq₀) (C-fmap n hY) (C-fmap n hX)
  C-seq-emap n (seq , seq-ise) = C-seq-fmap n seq , C-seq-isemap n seq-ise
