{-# OPTIONS --without-K --rewriting --termination-depth=2 #-}

open import HoTT
open import cohomology.ChainComplex
open import cohomology.Theory
open import groups.KernelImage
open import cw.CW

module cw.cohomology.ReconstructedHigherCohomologyGroups {i : ULevel} (OT : OrdinaryTheory i) where

  open OrdinaryTheory OT
  import cw.cohomology.HigherCoboundary OT as HC
  open import cw.cohomology.WedgeOfCells OT
  open import cw.cohomology.Descending OT
  open import cw.cohomology.ReconstructedCochainComplex OT
  import cw.cohomology.HigherCohomologyGroups OT as HCG
  import cw.cohomology.HigherCohomologyGroupsOnDiag OT as HCGD
  import cw.cohomology.CohomologyGroupsTooHigh OT as CGTH

  private
    ≤-dec-has-all-paths : {m n : ℕ} → has-all-paths (Dec (m ≤ n))
    ≤-dec-has-all-paths = prop-has-all-paths

  private
    abstract
      higher-cohomology-group-descend : ∀ {n} (⊙skel : ⊙Skeleton {i} (2 + n)) {m} (Sm<n : S m < n)
        →  cohomology-group (cochain-complex ⊙skel) (ℕ-to-ℤ (2 + m))
        == cohomology-group (cochain-complex (⊙cw-init ⊙skel)) (ℕ-to-ℤ (2 + m))
      higher-cohomology-group-descend ⊙skel {m} ltS -- n = 2 + m
        = ap3
            (λ Sm≤4+m? SSm≤4+m? SSSm≤4+m? → Ker/Im
              (coboundary-template ⊙skel SSm≤4+m? SSSm≤4+m?)
              (coboundary-template ⊙skel Sm≤4+m? SSm≤4+m?)
              (cochain-is-abelian-template ⊙skel SSm≤4+m?))
            (≤-dec-has-all-paths (≤-dec (1 + m) (4 + m)) (inl (lteSR $ lteSR lteS)))
            (≤-dec-has-all-paths (≤-dec (2 + m) (4 + m)) (inl (lteSR lteS)))
            (≤-dec-has-all-paths (≤-dec (3 + m) (4 + m)) (inl lteS))
        ∙ ap2 (λ δ₁ δ₂ → Ker/Im δ₂ δ₁ (CXₙ/Xₙ₋₁-is-abelian (⊙cw-take (lteSR lteS) ⊙skel) (ℕ-to-ℤ (2 + m))))
            (coboundary-higher-template-descend-from-far {n = 3 + m} ⊙skel {m = m} (ltSR ltS) ltS)
            (coboundary-higher-template-descend-from-one-above ⊙skel)
        ∙ ap3
            (λ Sm≤3+m? SSm≤3+m? SSSm≤3+m? → Ker/Im
              (coboundary-template (⊙cw-init ⊙skel) SSm≤3+m? SSSm≤3+m?)
              (coboundary-template (⊙cw-init ⊙skel) Sm≤3+m? SSm≤3+m?)
              (cochain-is-abelian-template (⊙cw-init ⊙skel) SSm≤3+m?))
            (≤-dec-has-all-paths (inl (lteSR lteS)) (≤-dec (1 + m) (3 + m)))
            (≤-dec-has-all-paths (inl lteS)         (≤-dec (2 + m) (3 + m)))
            (≤-dec-has-all-paths (inl lteE)         (≤-dec (3 + m) (3 + m)))
      higher-cohomology-group-descend {n = S n} ⊙skel {m} (ltSR Sm<n) -- n = S n
        = ap3
            (λ Sm≤3+n? SSm≤3+n? SSSm≤3+n? → Ker/Im
              (coboundary-template ⊙skel SSm≤3+n? SSSm≤3+n?)
              (coboundary-template ⊙skel Sm≤3+n? SSm≤3+n?)
              (cochain-is-abelian-template ⊙skel SSm≤3+n?))
            (≤-dec-has-all-paths (≤-dec (1 + m) (3 + n)) (inl (lteSR $ lteSR $ lteSR (inr Sm<n))))
            (≤-dec-has-all-paths (≤-dec (2 + m) (3 + n)) (inl (≤-+-l 1 (lteSR $ lteSR $ inr Sm<n))))
            (≤-dec-has-all-paths (≤-dec (3 + m) (3 + n)) (inl (≤-+-l 2 (lteSR (inr Sm<n)))))
        ∙ ap2
            (λ δ₁ δ₂ → Ker/Im δ₂ δ₁
              (CXₙ/Xₙ₋₁-is-abelian (⊙cw-take (≤-+-l 1 (lteSR $ lteSR $ inr Sm<n)) ⊙skel) (ℕ-to-ℤ (2 + m))))
            (coboundary-higher-template-descend-from-far {n = 2 + n} ⊙skel {m = m}   (ltSR (ltSR Sm<n))    (<-+-l 1 (ltSR Sm<n)))
            (coboundary-higher-template-descend-from-far {n = 2 + n} ⊙skel {m = S m} (<-+-l 1 (ltSR Sm<n)) (<-+-l 2 Sm<n))
        ∙ ap3
            (λ Sm≤2+n? SSm≤2+n? SSSm≤2+n? → Ker/Im
              (coboundary-template (⊙cw-init ⊙skel) SSm≤2+n? SSSm≤2+n?)
              (coboundary-template (⊙cw-init ⊙skel) Sm≤2+n? SSm≤2+n?)
              (cochain-is-abelian-template (⊙cw-init ⊙skel) SSm≤2+n?))
            (≤-dec-has-all-paths (inl (lteSR $ lteSR $ inr Sm<n))   (≤-dec (1 + m) (2 + n)))
            (≤-dec-has-all-paths (inl (≤-+-l 1 (lteSR $ inr Sm<n))) (≤-dec (2 + m) (2 + n)))
            (≤-dec-has-all-paths (inl (≤-+-l 2 (inr Sm<n)))         (≤-dec (3 + m) (2 + n)))

      higher-cohomology-group-β : ∀ {n} (⊙skel : ⊙Skeleton {i} (3 + n))
        →  cohomology-group (cochain-complex ⊙skel) (ℕ-to-ℤ (2 + n))
        == Ker/Im
            (HC.cw-co∂-last ⊙skel)
            (HC.cw-co∂-last (⊙cw-init ⊙skel))
            (CXₙ/Xₙ₋₁-is-abelian (⊙cw-init ⊙skel) (ℕ-to-ℤ (2 + n)))
      higher-cohomology-group-β {n} ⊙skel
        = ap3
            (λ 1+n≤3+n? 2+n≤3+n? 3+n≤3+n? → Ker/Im
              (coboundary-template ⊙skel 2+n≤3+n? 3+n≤3+n?)
              (coboundary-template ⊙skel 1+n≤3+n? 2+n≤3+n?)
              (cochain-is-abelian-template ⊙skel 2+n≤3+n?))
            (≤-dec-has-all-paths (≤-dec (1 + n) (3 + n)) (inl (lteSR lteS)))
            (≤-dec-has-all-paths (≤-dec (2 + n) (3 + n)) (inl lteS))
            (≤-dec-has-all-paths (≤-dec (3 + n) (3 + n)) (inl lteE))
        ∙ ap2 (λ δ₁ δ₂ → Ker/Im δ₂ δ₁ (CXₙ/Xₙ₋₁-is-abelian (⊙cw-init ⊙skel) (ℕ-to-ℤ (2 + n))))
            ( coboundary-higher-template-descend-from-one-above ⊙skel
            ∙ coboundary-higher-template-β (⊙cw-init ⊙skel))
            (coboundary-higher-template-β ⊙skel)

      higher-cohomology-group-β-one-below : ∀ {n} (⊙skel : ⊙Skeleton {i} (2 + n))
        →  cohomology-group (cochain-complex ⊙skel) (ℕ-to-ℤ (2 + n))
        == Ker/Im
            (cst-hom {H = Lift-group {j = i} Unit-group})
            (HC.cw-co∂-last ⊙skel)
            (CXₙ/Xₙ₋₁-is-abelian ⊙skel (ℕ-to-ℤ (2 + n)))
      higher-cohomology-group-β-one-below {n} ⊙skel
        = ap3
            (λ 1+n≤2+n? 2+n≤2+n? 3+n≤2+n? → Ker/Im
              (coboundary-template ⊙skel 2+n≤2+n? 3+n≤2+n?)
              (coboundary-template ⊙skel 1+n≤2+n? 2+n≤2+n?)
              (cochain-is-abelian-template ⊙skel 2+n≤2+n?))
            (≤-dec-has-all-paths (≤-dec (1 + n) (2 + n)) (inl lteS))
            (≤-dec-has-all-paths (≤-dec (2 + n) (2 + n)) (inl lteE))
            (≤-dec-has-all-paths (≤-dec (3 + n) (2 + n)) (inr (<-to-≱ ltS)))
        ∙ ap
            (λ δ₁ → Ker/Im
              (cst-hom {H = Lift-group {j = i} Unit-group})
              δ₁ (CXₙ/Xₙ₋₁-is-abelian ⊙skel (ℕ-to-ℤ (2 + n))))
            (coboundary-higher-template-β ⊙skel)

      higher-cohomology-group-β-far-below : ∀ {n} (⊙skel : ⊙Skeleton {i} n) {m} (SSm≰n : ¬ (2 + m ≤ n))
        →  cohomology-group (cochain-complex ⊙skel) (ℕ-to-ℤ (2 + m))
        == Ker/Im
            (cst-hom {H = Lift-group {j = i} Unit-group})
            (cst-hom
              {G = AbGroup.grp (cochain-template ⊙skel (≤-dec (1 + m) n))}
              {H = Lift-group {j = i} Unit-group})
            (snd (Lift-abgroup {j = i} Unit-abgroup))
      higher-cohomology-group-β-far-below {n} ⊙skel {m} SSm≰n
        = ap2
            (λ 2+m≤n? 3+m≤n? → Ker/Im
              (coboundary-template ⊙skel 2+m≤n? 3+m≤n?)
              (coboundary-template ⊙skel (≤-dec (1 + m) n) 2+m≤n?)
              (cochain-is-abelian-template ⊙skel 2+m≤n?))
            (≤-dec-has-all-paths (≤-dec (2 + m) n) (inr SSm≰n))
            (≤-dec-has-all-paths (≤-dec (3 + m) n) (inr (λ SSSm≤n → SSm≰n (≤-trans lteS SSSm≤n))))

  abstract
    higher-cohomology-group : ∀ m {n} (⊙skel : ⊙Skeleton {i} n)
      → ⊙has-cells-with-choice 0 ⊙skel i
      → C (ℕ-to-ℤ (2 + m)) ⊙⟦ ⊙skel ⟧ ≃ᴳ cohomology-group (cochain-complex ⊙skel) (ℕ-to-ℤ (2 + m))
    higher-cohomology-group m {n = 0} ⊙skel ac =
      CGTH.C-cw-iso-ker/im (2 + m) (O<S (S m)) (Lift-group {j = i} Unit-group) ⊙skel ac
    higher-cohomology-group m {n = 1} ⊙skel ac =
      CGTH.C-cw-iso-ker/im (2 + m) (<-+-l 1 (O<S m))
        (AbGroup.grp (cochain-template ⊙skel (≤-dec (1 + m) 1)))
        ⊙skel ac
    higher-cohomology-group m {n = S (S n)} ⊙skel ac with ℕ-trichotomy (S m) (S n)
    ... | inl idp = coe!ᴳ-iso (higher-cohomology-group-β-one-below ⊙skel)
                ∘eᴳ HCGD.C-cw-iso-ker/im ⊙skel ac
    ... | inr (inl ltS) = coe!ᴳ-iso (higher-cohomology-group-β ⊙skel)
                      ∘eᴳ HCG.C-cw-iso-ker/im ⊙skel ac
    ... | inr (inl (ltSR Sm<n)) =
                coe!ᴳ-iso (higher-cohomology-group-descend ⊙skel Sm<n)
            ∘eᴳ higher-cohomology-group m {n = S n} (⊙cw-init ⊙skel) (⊙init-has-cells-with-choice ⊙skel ac)
            ∘eᴳ C-cw-descend-at-lower ⊙skel (<-+-l 1 Sm<n) ac
    ... | inr (inr Sn<Sm) =
                coe!ᴳ-iso (higher-cohomology-group-β-far-below ⊙skel (<-to-≱ (<-+-l 1 Sn<Sm)))
            ∘eᴳ CGTH.C-cw-iso-ker/im (2 + m) (<-+-l 1 Sn<Sm)
                  (AbGroup.grp (cochain-template ⊙skel (≤-dec (1 + m) (2 + n))))
                  ⊙skel ac
