{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cw.CW
open import cw.FinCW
open import cw.FinBoundary
open import cohomology.Theory
open import cohomology.ChainComplex

module cw.cohomology.ReconstructedCochainsEquivCellularCochains
  (OT : OrdinaryTheory lzero) where

  open OrdinaryTheory OT
  open import cw.cohomology.cellular.ChainComplex as CCC
  open import cw.cohomology.reconstructed.cochain.Complex OT as RCC
  open import cw.cohomology.ReconstructedCochainsIsoCellularCochains OT
  open import cw.cohomology.cochainequiv.AugmentCommSquare OT
  open import cw.cohomology.cochainequiv.FirstCoboundaryCommSquare OT
  open import cw.cohomology.cochainequiv.HigherCoboundaryCommSquare OT

  private
    frcc-comm-fccc-Type : ∀ {n} (⊙fin-skel : ⊙FinSkeleton n)
      {m} (m≤n? : Dec (m ≤ n)) (Sm≤n? : Dec (S m ≤ n))
      (coboundary : AbGroup.grp (RCC.cochain-template ⊙⦉ ⊙fin-skel ⦊ m≤n?)
                 →ᴳ AbGroup.grp (RCC.cochain-template ⊙⦉ ⊙fin-skel ⦊ Sm≤n?))
      (boundary : AbGroup.grp (CCC.chain-template ⦉ ⊙FinSkeleton.skel ⊙fin-skel ⦊ Sm≤n?)
               →ᴳ AbGroup.grp (CCC.chain-template ⦉ ⊙FinSkeleton.skel ⊙fin-skel ⦊ m≤n?))
      → Type₀
    frcc-comm-fccc-Type {n} ⊙fin-skel {m} m≤n? Sm≤n? coboundary boundary =
      CommSquareᴳ
        coboundary
        (pre∘ᴳ-hom (C2-abgroup 0) boundary)
        (GroupIso.f-hom (rcc-iso-ccc-template ⊙⦉ ⊙fin-skel ⦊ m≤n?
          (⊙FinSkeleton-has-cells-with-choice 0 ⊙fin-skel lzero)))
        (GroupIso.f-hom (rcc-iso-ccc-template ⊙⦉ ⊙fin-skel ⦊ Sm≤n?
          (⊙FinSkeleton-has-cells-with-choice 0 ⊙fin-skel lzero)))

    CCC-boundary-template' : ∀ {n} (⊙fin-skel : ⊙FinSkeleton n)
      → {m : ℕ} (m≤n? : Dec (m ≤ n)) (Sm≤n? : Dec (S m ≤ n))
      →  AbGroup.grp (CCC.chain-template ⦉ ⊙FinSkeleton.skel ⊙fin-skel ⦊ Sm≤n?)
      →ᴳ AbGroup.grp (CCC.chain-template ⦉ ⊙FinSkeleton.skel ⊙fin-skel ⦊ m≤n?)
    CCC-boundary-template' ⊙fin-skel =
      CCC.boundary-template ⦉ ⊙FinSkeleton.skel ⊙fin-skel ⦊
        (FinSkeleton-has-cells-with-dec-eq (⊙FinSkeleton.skel ⊙fin-skel))
        (FinSkeleton-has-degrees-with-finite-support (⊙FinSkeleton.skel ⊙fin-skel))

    RCC-coboundary-template' : ∀ {n} (⊙fin-skel : ⊙FinSkeleton n)
      → {m : ℕ} (m≤n? : Dec (m ≤ n)) (Sm≤n? : Dec (S m ≤ n))
      →  AbGroup.grp (RCC.cochain-template ⊙⦉ ⊙fin-skel ⦊ m≤n?)
      →ᴳ AbGroup.grp (RCC.cochain-template ⊙⦉ ⊙fin-skel ⦊ Sm≤n?)
    RCC-coboundary-template' ⊙fin-skel = RCC.coboundary-template ⊙⦉ ⊙fin-skel ⦊

    abstract
      {- This can be directly generalized to the non-finite cases. -}
      frcc-comm-fccc-above : ∀ {n} (⊙fin-skel : ⊙FinSkeleton n)
          {m} (m≤n? : Dec (m ≤ n)) (Sm≰n : ¬ (S m ≤ n))
        → frcc-comm-fccc-Type ⊙fin-skel m≤n? (inr Sm≰n)
            (RCC-coboundary-template' ⊙fin-skel m≤n? (inr Sm≰n))
            (CCC-boundary-template' ⊙fin-skel m≤n? (inr Sm≰n))
      frcc-comm-fccc-above ⊙fin-skel m≤n? Sm≰n =
        (comm-sqrᴳ λ g → group-hom= $ λ= λ _ →
          ! $ GroupHom.pres-ident
            (GroupIso.f
              (rcc-iso-ccc-template ⊙⦉ ⊙fin-skel ⦊ m≤n?
              (⊙FinSkeleton-has-cells-with-choice 0 ⊙fin-skel lzero)) g))

      frcc-comm-fccc-nth : ∀ {n} (⊙fin-skel : ⊙FinSkeleton n) {m} (m≤n : m ≤ n) (Sm≤n : S m ≤ n)
        → frcc-comm-fccc-Type ⊙fin-skel (inl m≤n) (inl Sm≤n)
            (RCC-coboundary-template' ⊙fin-skel (inl m≤n) (inl Sm≤n))
            (CCC-boundary-template' ⊙fin-skel (inl m≤n) (inl Sm≤n))
      frcc-comm-fccc-nth ⊙fin-skel (inl idp) (inl Sm=m) = ⊥-rec (<-to-≠ ltS (! Sm=m))
      frcc-comm-fccc-nth ⊙fin-skel (inl idp) (inr Sm<m) = ⊥-rec (<-to-≠ (<-trans Sm<m ltS) idp)
      frcc-comm-fccc-nth ⊙fin-skel {m = O} (inr ltS) (inl 1=1) =
        transport!
          (λ 1=1 → frcc-comm-fccc-Type ⊙fin-skel (inl lteS) (inl (inl 1=1))
              (RCC-coboundary-template' ⊙fin-skel (inl lteS) (inl (inl 1=1)))
              (CCC-boundary-template' ⊙fin-skel (inl lteS) (inl (inl 1=1))))
          (prop-has-all-paths 1=1 idp)
          (coe!
            (ap2 (λ p₁ p₂ → frcc-comm-fccc-Type ⊙fin-skel {m = O} (inl (inr ltS)) (inl (inl idp)) p₁ p₂)
              (RCC.coboundary-first-template-β ⊙⦉ ⊙fin-skel ⦊)
              (CCC.boundary-template-β ⦉ ⊙FinSkeleton.skel ⊙fin-skel ⦊
                (FinSkeleton-has-cells-with-dec-eq (⊙FinSkeleton.skel ⊙fin-skel))
                (FinSkeleton-has-degrees-with-finite-support (⊙FinSkeleton.skel ⊙fin-skel))))
            (fst (first-coboundary-comm-sqrᴳ ⊙fin-skel)))
      frcc-comm-fccc-nth ⊙fin-skel {m = S m} (inr ltS) (inl SSm=SSm) =
        transport!
          (λ SSm=SSm → frcc-comm-fccc-Type ⊙fin-skel (inl lteS) (inl (inl SSm=SSm))
            (RCC-coboundary-template' ⊙fin-skel (inl lteS) (inl (inl SSm=SSm)))
            (CCC-boundary-template' ⊙fin-skel (inl lteS) (inl (inl SSm=SSm))))
          (prop-has-all-paths SSm=SSm idp)
          (coe!
            (ap2 (λ p₁ p₂ → frcc-comm-fccc-Type ⊙fin-skel {m = S m} (inl (inr ltS)) (inl (inl idp)) p₁ p₂)
              (RCC.coboundary-higher-template-β ⊙⦉ ⊙fin-skel ⦊)
              (CCC.boundary-template-β ⦉ ⊙FinSkeleton.skel ⊙fin-skel ⦊
                (FinSkeleton-has-cells-with-dec-eq (⊙FinSkeleton.skel ⊙fin-skel))
                (FinSkeleton-has-degrees-with-finite-support (⊙FinSkeleton.skel ⊙fin-skel))))
            (fst (higher-coboundary-comm-sqrᴳ ⊙fin-skel)))
      frcc-comm-fccc-nth ⊙fin-skel (inr ltS) (inr Sm<Sm) = ⊥-rec (<-to-≠ Sm<Sm idp)
      frcc-comm-fccc-nth ⊙fin-skel (inr (ltSR n<m)) (inl Sn=Sm) = ⊥-rec (<-to-≠ (<-ap-S n<m) Sn=Sm)
      frcc-comm-fccc-nth ⊙fin-skel {m = O} (inr (ltSR ltS)) (inr Sm<SSm) =
        transport!
          (λ Sm<SSm → frcc-comm-fccc-Type ⊙fin-skel (inl (inr (ltSR ltS))) (inl (inr Sm<SSm))
            (RCC-coboundary-template' ⊙fin-skel (inl (inr (ltSR ltS))) (inl (inr Sm<SSm)))
            (CCC-boundary-template' ⊙fin-skel (inl (inr (ltSR ltS))) (inl (inr Sm<SSm))))
          (prop-has-all-paths Sm<SSm ltS)
          (coe!
            (ap2 (λ p₁ p₂ → frcc-comm-fccc-Type ⊙fin-skel (inl (inr (ltSR ltS))) (inl (inr ltS)) p₁ p₂)
              (RCC.coboundary-first-template-descend-from-two ⊙⦉ ⊙fin-skel ⦊)
              (CCC.boundary-template-descend-from-two-above ⦉ ⊙FinSkeleton.skel ⊙fin-skel ⦊
                (FinSkeleton-has-cells-with-dec-eq (⊙FinSkeleton.skel ⊙fin-skel))
                (FinSkeleton-has-degrees-with-finite-support (⊙FinSkeleton.skel ⊙fin-skel))))
            (frcc-comm-fccc-nth (⊙fcw-init ⊙fin-skel) (inr ltS) (inl idp)))
      frcc-comm-fccc-nth ⊙fin-skel {m = S m} (inr (ltSR ltS)) (inr Sm<SSm) =
        transport!
          (λ Sm<SSm → frcc-comm-fccc-Type ⊙fin-skel (inl (inr (ltSR ltS))) (inl (inr Sm<SSm))
            (RCC-coboundary-template' ⊙fin-skel (inl (inr (ltSR ltS))) (inl (inr Sm<SSm)))
            (CCC-boundary-template' ⊙fin-skel (inl (inr (ltSR ltS))) (inl (inr Sm<SSm))))
          (prop-has-all-paths Sm<SSm ltS)
          (coe!
            (ap2 (λ p₁ p₂ → frcc-comm-fccc-Type ⊙fin-skel (inl (inr (ltSR ltS))) (inl (inr ltS)) p₁ p₂)
              (RCC.coboundary-higher-template-descend-from-one-above ⊙⦉ ⊙fin-skel ⦊)
              (CCC.boundary-template-descend-from-two-above ⦉ ⊙FinSkeleton.skel ⊙fin-skel ⦊
                (FinSkeleton-has-cells-with-dec-eq (⊙FinSkeleton.skel ⊙fin-skel))
                (FinSkeleton-has-degrees-with-finite-support (⊙FinSkeleton.skel ⊙fin-skel))))
            (frcc-comm-fccc-nth (⊙fcw-init ⊙fin-skel) (inr ltS) (inl idp)))
      frcc-comm-fccc-nth ⊙fin-skel (inr (ltSR (ltSR m<m))) (inr ltS) = ⊥-rec (<-to-≠ m<m idp)
      frcc-comm-fccc-nth ⊙fin-skel {m = O} (inr (ltSR (ltSR m<n))) (inr (ltSR SSm<Sn)) =
        (coe!
          (ap2 (λ p₁ p₂ → frcc-comm-fccc-Type ⊙fin-skel (inl (inr (ltSR (ltSR m<n)))) (inl (inr (ltSR SSm<Sn))) p₁ p₂)
            (RCC.coboundary-first-template-descend-from-far ⊙⦉ ⊙fin-skel ⦊ (ltSR m<n) SSm<Sn)
            (CCC.boundary-template-descend-from-far ⦉ ⊙FinSkeleton.skel ⊙fin-skel ⦊
              (FinSkeleton-has-cells-with-dec-eq (⊙FinSkeleton.skel ⊙fin-skel))
              (FinSkeleton-has-degrees-with-finite-support (⊙FinSkeleton.skel ⊙fin-skel))
              (ltSR m<n) SSm<Sn))
          (frcc-comm-fccc-nth (⊙fcw-init ⊙fin-skel) (inr (ltSR m<n)) (inr SSm<Sn)))
      frcc-comm-fccc-nth ⊙fin-skel {m = S m} (inr (ltSR (ltSR m<n))) (inr (ltSR SSm<Sn)) =
        (coe!
          (ap2 (λ p₁ p₂ → frcc-comm-fccc-Type ⊙fin-skel (inl (inr (ltSR (ltSR m<n)))) (inl (inr (ltSR SSm<Sn))) p₁ p₂)
            (RCC.coboundary-higher-template-descend-from-far ⊙⦉ ⊙fin-skel ⦊ (ltSR m<n) SSm<Sn)
            (CCC.boundary-template-descend-from-far ⦉ ⊙FinSkeleton.skel ⊙fin-skel ⦊
              (FinSkeleton-has-cells-with-dec-eq (⊙FinSkeleton.skel ⊙fin-skel))
              (FinSkeleton-has-degrees-with-finite-support (⊙FinSkeleton.skel ⊙fin-skel))
              (ltSR m<n) SSm<Sn))
          (frcc-comm-fccc-nth (⊙fcw-init ⊙fin-skel) (inr (ltSR m<n)) (inr SSm<Sn)))

      frcc-comm-fccc-template : ∀ {n} (⊙fin-skel : ⊙FinSkeleton n)
          {m} (m≤n? : Dec (m ≤ n)) (Sm≤n? : Dec (S m ≤ n))
        → frcc-comm-fccc-Type ⊙fin-skel m≤n? Sm≤n?
            (RCC-coboundary-template' ⊙fin-skel m≤n? Sm≤n?)
            (CCC-boundary-template' ⊙fin-skel m≤n? Sm≤n?)
      frcc-comm-fccc-template ⊙fin-skel m≤n? (inr Sm≰n) = frcc-comm-fccc-above ⊙fin-skel m≤n? Sm≰n
      frcc-comm-fccc-template ⊙fin-skel (inr m≰n) (inl Sm≤n) = ⊥-rec $ m≰n (≤-trans lteS Sm≤n)
      frcc-comm-fccc-template ⊙fin-skel (inl m≤n) (inl Sm≤n) = frcc-comm-fccc-nth ⊙fin-skel m≤n Sm≤n

      frcc-comm-fccc : ∀ {n} (⊙fin-skel : ⊙FinSkeleton n) m
        → frcc-comm-fccc-Type ⊙fin-skel (≤-dec m n) (≤-dec (S m) n)
            (RCC-coboundary-template' ⊙fin-skel (≤-dec m n) (≤-dec (S m) n))
            (CCC-boundary-template' ⊙fin-skel (≤-dec m n) (≤-dec (S m) n))
      frcc-comm-fccc {n} ⊙fin-skel m =
        frcc-comm-fccc-template ⊙fin-skel {m} (≤-dec m n) (≤-dec (S m) n)

      frcc-comm-fccc-augment : ∀ {n} (⊙fin-skel : ⊙FinSkeleton n)
        → CommSquareᴳ
            (CochainComplex.augment (RCC.cochain-complex ⊙⦉ ⊙fin-skel ⦊))
            (pre∘ᴳ-hom (C2-abgroup 0) (FreeAbGroup-extend (Lift-abgroup {j = lzero} ℤ-abgroup) λ _ → lift 1))
            (GroupIso.f-hom rhead-iso-chead)
            (GroupIso.f-hom (rcc-iso-ccc-template ⊙⦉ ⊙fin-skel ⦊ (inl (O≤ n))
              (⊙FinSkeleton-has-cells-with-choice 0 ⊙fin-skel lzero)))
      frcc-comm-fccc-augment {n = O} ⊙fin-skel =
        fst (augment-comm-sqrᴳ ⊙fin-skel)
      frcc-comm-fccc-augment {n = S O} ⊙fin-skel =
        frcc-comm-fccc-augment (⊙fcw-init ⊙fin-skel)
      frcc-comm-fccc-augment {n = S (S n)} ⊙fin-skel =
        frcc-comm-fccc-augment (⊙fcw-init ⊙fin-skel)

  frcc-equiv-fccc : ∀ {n} (⊙fin-skel : ⊙FinSkeleton n) →
    CochainComplexEquiv
      (RCC.cochain-complex ⊙⦉ ⊙fin-skel ⦊)
      (CCC.cochain-complex ⦉ ⊙FinSkeleton.skel ⊙fin-skel ⦊
         (FinSkeleton-has-cells-with-dec-eq (⊙FinSkeleton.skel ⊙fin-skel))
         (FinSkeleton-has-degrees-with-finite-support (⊙FinSkeleton.skel ⊙fin-skel))
         (C2-abgroup 0))
  frcc-equiv-fccc {n} ⊙fin-skel = record
    { head = rhead-iso-chead
    ; cochain = λ m → rcc-iso-ccc ⊙⦉ ⊙fin-skel ⦊ m (⊙FinSkeleton-has-cells-with-choice 0 ⊙fin-skel lzero)
    ; augment = frcc-comm-fccc-augment ⊙fin-skel
    ; coboundary = frcc-comm-fccc ⊙fin-skel}

  frc-iso-fcc : ∀ {n} (⊙fin-skel : ⊙FinSkeleton n) (m : ℤ)
    →  cohomology-group (RCC.cochain-complex ⊙⦉ ⊙fin-skel ⦊) m
    ≃ᴳ cohomology-group
        (CCC.cochain-complex ⦉ ⊙FinSkeleton.skel ⊙fin-skel ⦊
          (FinSkeleton-has-cells-with-dec-eq (⊙FinSkeleton.skel ⊙fin-skel))
          (FinSkeleton-has-degrees-with-finite-support (⊙FinSkeleton.skel ⊙fin-skel))
          (C2-abgroup 0))
        m
  frc-iso-fcc ⊙fin-skel = cohomology-group-emap (frcc-equiv-fccc ⊙fin-skel)
