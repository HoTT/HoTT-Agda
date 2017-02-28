{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.ChainComplex
open import cohomology.Theory
open import cw.CW

module cw.cohomology.ReconstructedCochainComplex2 {i : ULevel} (OT : OrdinaryTheory i) where

  open OrdinaryTheory OT
  import cw.cohomology.CoboundaryGrid OT as CG
  import cw.cohomology.TipAndAugment OT as TAA
  import cw.cohomology.TipGrid OT as TG
  open import cw.cohomology.ReconstructedCochainComplex OT
  import cw.cohomology.ZerothCohomologyGroup OT as ZCG
  import cw.cohomology.ZerothCohomologyGroupOnDiag OT as ZCGD

  private
    abstract
      path-lemma₀ : ∀ {n} (⊙skel : ⊙Skeleton {i} (S n)) {m} (m<n : m < n) (Sm<n : S m < n)
        →  ap (λ m≤Sn → ⊙cw-take m≤Sn ⊙skel) (≤-has-all-paths (≤-trans lteS (lteSR (inr Sm<n))) (lteSR (inr m<n)))
        == ap (λ m≤n → ⊙cw-take m≤n (⊙cw-init ⊙skel)) (≤-has-all-paths (≤-trans lteS (inr Sm<n)) (inr m<n))
      path-lemma₀ ⊙skel m<n Sm<n =
        ap (λ m≤Sn → ⊙cw-take m≤Sn ⊙skel) (≤-has-all-paths (≤-trans lteS (lteSR (inr Sm<n))) (lteSR (inr m<n)))
          =⟨ ap (ap (λ m≤Sn → ⊙cw-take m≤Sn ⊙skel)) (contr-has-all-paths (≤-is-prop _ _) _ _) ⟩
        ap (λ m≤Sn → ⊙cw-take m≤Sn ⊙skel) (ap (lteSR ∘ inr) (<-has-all-paths (<-trans ltS Sm<n) m<n))
          =⟨ ∘-ap (λ m≤Sn → ⊙cw-take m≤Sn ⊙skel) (lteSR ∘ inr) _ ⟩
        ap (λ Sm<n → ⊙cw-take (lteSR (inr Sm<n)) ⊙skel) (<-has-all-paths (<-trans ltS Sm<n) m<n)
          =⟨ ap-∘ (λ m≤n → ⊙cw-take m≤n (⊙cw-init ⊙skel)) inr _ ⟩
        ap (λ m≤n → ⊙cw-take m≤n (⊙cw-init ⊙skel)) (ap inr (<-has-all-paths (<-trans ltS Sm<n) m<n))
          =⟨ ap (ap (λ m≤n → ⊙cw-take m≤n (⊙cw-init ⊙skel))) (contr-has-all-paths (≤-is-prop _ _) _ _) ⟩
        ap (λ m≤n → ⊙cw-take m≤n (⊙cw-init ⊙skel)) (≤-has-all-paths (≤-trans lteS (inr Sm<n)) (inr m<n))
          =∎

      path-lemma₁ : ∀ {n} (⊙skel : ⊙Skeleton {i} (S (S n)))
        →  ap (λ n≤SSn → ⊙cw-take n≤SSn ⊙skel) (≤-has-all-paths (lteSR lteS) (lteSR lteS))
        == ap (λ n≤Sn → ⊙cw-take n≤Sn (⊙cw-init ⊙skel)) (≤-has-all-paths lteS lteS)
      path-lemma₁ ⊙skel =
        ap (λ n≤SSn → ⊙cw-take n≤SSn ⊙skel) (≤-has-all-paths (lteSR lteS) (lteSR lteS))
          =⟨ ap (ap (λ n≤SSn → ⊙cw-take n≤SSn ⊙skel)) (contr-has-all-paths (≤-is-prop _ _) _ _) ⟩
        idp
          =⟨ ap (ap (λ n≤Sn → ⊙cw-take n≤Sn (⊙cw-init ⊙skel))) (contr-has-all-paths (≤-is-prop _ _) _ _) ⟩
        ap (λ n≤Sn → ⊙cw-take n≤Sn (⊙cw-init ⊙skel)) (≤-has-all-paths lteS lteS)
          =∎

      path-lemma₂ : ∀ {n} (⊙skel : ⊙Skeleton {i} (S n))
        → ap (λ n≤Sn → ⊙cw-take n≤Sn ⊙skel) (≤-has-all-paths lteS lteS) == idp
      path-lemma₂ ⊙skel =
        ap (λ n≤Sn → ⊙cw-take n≤Sn ⊙skel) (≤-has-all-paths lteS lteS)
          =⟨ ap (ap (λ n≤Sn → ⊙cw-take n≤Sn ⊙skel)) (contr-has-all-paths (≤-is-prop _ _) _ _) ⟩
        idp
          =∎

    abstract
      coboundary-first-template-descend-from-far : ∀ {n} (⊙skel : ⊙Skeleton {i} (S n)) ac 0<n 1<n
        → coboundary-hom-template {n = S n} ⊙skel ac (inl (lteSR (inr 0<n))) (inl (lteSR (inr 1<n)))
          == coboundary-hom-template {n = n} (⊙cw-init ⊙skel)
            (⊙init-has-cells-with-choice ⊙skel ac)
            (inl (inr 0<n)) (inl (inr 1<n))
      coboundary-first-template-descend-from-far ⊙skel ac 0<n 1<n = group-hom= $
        ap (coboundary-first-template ⊙skel ac (lteSR (inr 0<n)) (lteSR (inr 1<n)) (⊙cw-init-take (lteSR (inr 1<n)) ⊙skel))
          (path-lemma₀ ⊙skel 0<n 1<n)

      coboundary-first-template-descend-from-two : ∀ (⊙skel : ⊙Skeleton {i} 2) ac
        → coboundary-hom-template {n = 2} ⊙skel ac (inl (lteSR lteS)) (inl lteS)
          == coboundary-hom-template {n = 1} (⊙cw-init ⊙skel)
            (⊙init-has-cells-with-choice ⊙skel ac)
            (inl lteS) (inl lteE)
      coboundary-first-template-descend-from-two ⊙skel ac = group-hom= $
        ap (coboundary-first-template ⊙skel ac (lteSR lteS) lteS idp) (path-lemma₁ ⊙skel)

      coboundary-first-template-β : ∀ (⊙skel : ⊙Skeleton {i} 1) ac
        →  coboundary-hom-template {n = 1} ⊙skel ac (inl lteS) (inl lteE)
        == TG.cw-co∂-head ⊙skel ac
      coboundary-first-template-β ⊙skel ac = group-hom= $
        ap (coboundary-first-template ⊙skel ac lteS lteE idp) (path-lemma₂ ⊙skel)

  abstract
    zeroth-cohomology-group-descend : ∀ {n} (⊙skel : ⊙Skeleton {i} (S (S n))) ac
      →  cohomology-group (cochain-complex ⊙skel ac) 0
      == cohomology-group (cochain-complex (⊙cw-init ⊙skel) (⊙init-has-cells-with-choice ⊙skel ac)) 0
    zeroth-cohomology-group-descend {n = O} ⊙skel ac
      = ap (λ coboundary → QuotGroup (quot-of-sub (ker-propᴳ coboundary) (im-npropᴳ cc.augment (snd (cc.cochain 0)))))
          (coboundary-first-template-descend-from-two ⊙skel ac)
      where module cc = CochainComplex (cochain-complex ⊙skel ac)
    zeroth-cohomology-group-descend {n = S n} ⊙skel ac
      = ap (λ coboundary → QuotGroup (quot-of-sub (ker-propᴳ coboundary) (im-npropᴳ cc.augment (snd (cc.cochain 0)))))
          (coboundary-first-template-descend-from-far ⊙skel ac (ltSR (O<S n)) (<-ap-S (O<S n)))
      where module cc = CochainComplex (cochain-complex ⊙skel ac)

    zeroth-cohomology-group-β : ∀ (⊙skel : ⊙Skeleton {i} 1) ac
      →  cohomology-group (cochain-complex ⊙skel ac) 0
      == QuotGroup (quot-of-sub
          (ker-propᴳ (TG.cw-co∂-head ⊙skel ac))
          (im-npropᴳ (TAA.cw-coε (⊙cw-init ⊙skel)) (snd (CochainComplex.cochain (cochain-complex ⊙skel ac) 0))))
    zeroth-cohomology-group-β ⊙skel ac
      = ap (λ coboundary → QuotGroup (quot-of-sub (ker-propᴳ coboundary) (im-npropᴳ cc.augment (snd (cc.cochain 0)))))
          (coboundary-first-template-β ⊙skel ac)
      where module cc = CochainComplex (cochain-complex ⊙skel ac)
