{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.ChainComplex
open import cohomology.Theory
open import groups.KernelImage
open import cw.CW

module cw.cohomology.ReconstructedCochainComplex {i : ULevel} (OT : OrdinaryTheory i) where

  open OrdinaryTheory OT
  import cw.cohomology.CoboundaryGrid OT as CG
  import cw.cohomology.TipAndAugment OT as TAA
  import cw.cohomology.TipGrid OT as TG
  open import cw.cohomology.Descending OT
  import cw.cohomology.ZerothCohomologyGroup OT as ZCG
  import cw.cohomology.ZerothCohomologyGroupOnDiag OT as ZCGD

  cochain-template : ∀ {n} (⊙skel : ⊙Skeleton {i} n) {m}
    → Dec (m ≤ n) → AbGroup i
  cochain-template ⊙skel (inr _) = Lift-abgroup {j = i} Unit-abgroup
  cochain-template ⊙skel {m = 0} (inl 0≤n) = TAA.G×CX₀-abgroup (⊙cw-take 0≤n ⊙skel)
  cochain-template ⊙skel {m = S m} (inl Sm≤n) = C-abgroup (ℕ-to-ℤ (S m)) (⊙Cofiber (⊙cw-incl-nth Sm≤n ⊙skel))

  coboundary-nth-template : ∀ {n} (⊙skel : ⊙Skeleton {i} n)
    → ⊙has-cells-with-choice 0 ⊙skel i
    → {m : ℕ} (Sm≤n : S m ≤ n) (SSm≤n : S (S m) ≤ n)
    → ⊙cw-init (⊙cw-take SSm≤n ⊙skel) == ⊙cw-take (≤-trans lteS SSm≤n) ⊙skel
    → ⊙cw-take (≤-trans lteS SSm≤n) ⊙skel == ⊙cw-take Sm≤n ⊙skel
    → CEl (ℕ-to-ℤ (S m)) (⊙Cofiber (⊙cw-incl-nth Sm≤n ⊙skel))
    → CEl (ℕ-to-ℤ (S (S m))) (⊙Cofiber (⊙cw-incl-nth SSm≤n ⊙skel))
  coboundary-nth-template ⊙skel ac {m} Sm≤n SSm≤n path₀ path₁ =
      GroupHom.f (CG.cw-co∂-last (⊙cw-take SSm≤n ⊙skel) (⊙take-has-cells-with-choice SSm≤n ⊙skel ac))
    ∘ transport! (λ ⊙skel → CEl (ℕ-to-ℤ (S m)) (⊙Cofiber (⊙cw-incl-last ⊙skel))) (path₀ ∙ path₁)

  abstract
    coboundary-pres-comp-nth-template : ∀ {n} (⊙skel : ⊙Skeleton {i} n) ac {m} Sm≤n SSm≤n path₀ path₁
      → preserves-comp
          (Group.comp (C (ℕ-to-ℤ (S m)) (⊙Cofiber (⊙cw-incl-nth Sm≤n ⊙skel))))
          (Group.comp (C (ℕ-to-ℤ (S (S m))) (⊙Cofiber (⊙cw-incl-nth SSm≤n ⊙skel))))
          (coboundary-nth-template ⊙skel ac Sm≤n SSm≤n path₀ path₁)
    coboundary-pres-comp-nth-template ⊙skel ac {m} Sm≤n SSm≤n path₀ path₁ =
      ∘-pres-comp
        (CG.cw-co∂-last (⊙cw-take SSm≤n ⊙skel) (⊙take-has-cells-with-choice SSm≤n ⊙skel ac))
        (transport!ᴳ (λ ⊙skel → C (ℕ-to-ℤ (S m)) (⊙Cofiber (⊙cw-incl-last ⊙skel))) (path₀ ∙ path₁))

  coboundary-hom-nth-template : ∀ {n} (⊙skel : ⊙Skeleton {i} n)
    → ⊙has-cells-with-choice 0 ⊙skel i
    → {m : ℕ} (Sm≤n : S m ≤ n) (SSm≤n : S (S m) ≤ n)
    → ⊙cw-init (⊙cw-take SSm≤n ⊙skel) == ⊙cw-take (≤-trans lteS SSm≤n) ⊙skel
    → ⊙cw-take (≤-trans lteS SSm≤n) ⊙skel == ⊙cw-take Sm≤n ⊙skel
    →  C (ℕ-to-ℤ (S m)) (⊙Cofiber (⊙cw-incl-nth Sm≤n ⊙skel))
    →ᴳ C (ℕ-to-ℤ (S (S m))) (⊙Cofiber (⊙cw-incl-nth SSm≤n ⊙skel))
  coboundary-hom-nth-template ⊙skel ac Sm≤n SSm≤n path₀ path₁ = record {
    f = coboundary-nth-template ⊙skel ac Sm≤n SSm≤n path₀ path₁;
    pres-comp = coboundary-pres-comp-nth-template ⊙skel ac Sm≤n SSm≤n path₀ path₁}

  coboundary-first-template : ∀ {n} (⊙skel : ⊙Skeleton {i} n)
    → ⊙has-cells-with-choice 0 ⊙skel i
    → (0≤n : 0 ≤ n) (1≤n : 1 ≤ n)
    → ⊙cw-init (⊙cw-take 1≤n ⊙skel) == ⊙cw-take (≤-trans lteS 1≤n) ⊙skel
    → ⊙cw-take (≤-trans lteS 1≤n) ⊙skel == ⊙cw-take 0≤n ⊙skel
    → Group.El (TAA.G×CX₀ (⊙cw-take 0≤n ⊙skel))
    → CEl 1 (⊙Cofiber (⊙cw-incl-nth 1≤n ⊙skel))
  coboundary-first-template ⊙skel ac 0≤n 1≤n path₀ path₁ =
      GroupHom.f (TG.cw-co∂-head (⊙cw-take 1≤n ⊙skel) (⊙take-has-cells-with-choice 1≤n ⊙skel ac))
    ∘ transport! (λ ⊙skel → Group.El (TAA.G×CX₀ ⊙skel)) (path₀ ∙ path₁)

  abstract
    coboundary-pres-comp-first-template : ∀ {n} (⊙skel : ⊙Skeleton {i} n) ac 0≤n 1≤n path₀ path₁
      → preserves-comp
          (Group.comp (TAA.G×CX₀ (⊙cw-take 0≤n ⊙skel)))
          (Group.comp (C 1 (⊙Cofiber (⊙cw-incl-nth 1≤n ⊙skel))))
          (coboundary-first-template ⊙skel ac 0≤n 1≤n path₀ path₁)
    coboundary-pres-comp-first-template ⊙skel ac 0≤n 1≤n path₀ path₁ = ∘-pres-comp
      (TG.cw-co∂-head (⊙cw-take 1≤n ⊙skel) (⊙take-has-cells-with-choice 1≤n ⊙skel ac))
      (transport!ᴳ TAA.G×CX₀ (path₀ ∙ path₁))

  coboundary-hom-first-template : ∀ {n} (⊙skel : ⊙Skeleton {i} n)
    → ⊙has-cells-with-choice 0 ⊙skel i
    → (0≤n : 0 ≤ n) (1≤n : 1 ≤ n)
    → ⊙cw-init (⊙cw-take 1≤n ⊙skel) == ⊙cw-take (≤-trans lteS 1≤n) ⊙skel
    → ⊙cw-take (≤-trans lteS 1≤n) ⊙skel == ⊙cw-take 0≤n ⊙skel
    →  TAA.G×CX₀ (⊙cw-take 0≤n ⊙skel)
    →ᴳ C 1 (⊙Cofiber (⊙cw-incl-nth 1≤n ⊙skel))
  coboundary-hom-first-template ⊙skel ac 0≤n 1≤n path₀ path₁ = record {
    f = coboundary-first-template ⊙skel ac 0≤n 1≤n path₀ path₁;
    pres-comp = coboundary-pres-comp-first-template ⊙skel ac 0≤n 1≤n path₀ path₁}

  coboundary-hom-template : ∀ {n} (⊙skel : ⊙Skeleton {i} n)
    → ⊙has-cells-with-choice 0 ⊙skel i
    → {m : ℕ} (m≤n? : Dec (m ≤ n)) (Sm≤n? : Dec (S m ≤ n))
    → (AbGroup.grp (cochain-template ⊙skel m≤n?) →ᴳ AbGroup.grp (cochain-template ⊙skel Sm≤n?))
  coboundary-hom-template ⊙skel ac _ (inr _) = cst-hom
  coboundary-hom-template ⊙skel ac (inr m≰n) (inl Sm≤n) = ⊥-rec $ m≰n (≤-trans lteS Sm≤n)
  coboundary-hom-template ⊙skel ac {m = 0} (inl 0≤n) (inl 1≤n) =
    coboundary-hom-first-template ⊙skel ac 0≤n 1≤n (⊙cw-init-take 1≤n ⊙skel)
      (ap (λ 0≤n → ⊙cw-take 0≤n ⊙skel) (≤-has-all-paths (≤-trans lteS 1≤n) 0≤n))
  coboundary-hom-template ⊙skel ac {m = S m} (inl Sm≤n) (inl SSm≤n) =
    coboundary-hom-nth-template ⊙skel ac Sm≤n SSm≤n (⊙cw-init-take SSm≤n ⊙skel)
      (ap (λ Sm≤n → ⊙cw-take Sm≤n ⊙skel) (≤-has-all-paths (≤-trans lteS SSm≤n) Sm≤n))

  cochain-complex : ∀ {n} (⊙skel : ⊙Skeleton {i} n)
    → ⊙has-cells-with-choice 0 ⊙skel i
    → CochainComplex i
  cochain-complex {n} ⊙skel ac = record {M} where
    module M where
      head : AbGroup i
      head = C-abgroup 0 (⊙Lift ⊙Bool)

      cochain : ℕ → AbGroup i
      cochain m = cochain-template ⊙skel (≤-dec m n)

      augment : C 0 (⊙Lift ⊙Bool) →ᴳ AbGroup.grp (cochain 0)
      augment = TAA.cw-coε (⊙cw-take (O≤ n) ⊙skel)

      coboundary : ∀ m → (AbGroup.grp (cochain m) →ᴳ AbGroup.grp (cochain (S m)))
      coboundary m = coboundary-hom-template ⊙skel ac (≤-dec m n) (≤-dec (S m) n)

  {- lemmas of paths -}
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

      -- would be trivial with [≤-has-all-paths] defined with the set detection (issue #2003)
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

      -- would be trivial with [≤-has-all-paths] defined with the set detection (issue #2003)
      path-lemma₂ : ∀ {n} (⊙skel : ⊙Skeleton {i} (S n))
        → ap (λ n≤Sn → ⊙cw-take n≤Sn ⊙skel) (≤-has-all-paths lteS lteS) == idp
      path-lemma₂ ⊙skel =
        ap (λ n≤Sn → ⊙cw-take n≤Sn ⊙skel) (≤-has-all-paths lteS lteS)
          =⟨ ap (ap (λ n≤Sn → ⊙cw-take n≤Sn ⊙skel)) (contr-has-all-paths (≤-is-prop _ _) _ _) ⟩
        idp
          =∎

  {- lemmas of the first coboundary -}
  private
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

  {- lemmas of the zeroth cohomology group -}
  private
    abstract
      zeroth-cohomology-group-descend : ∀ {n} (⊙skel : ⊙Skeleton {i} (S (S n))) ac
        →  cohomology-group (cochain-complex ⊙skel ac) 0
        == cohomology-group (cochain-complex (⊙cw-init ⊙skel) (⊙init-has-cells-with-choice ⊙skel ac)) 0
      zeroth-cohomology-group-descend {n = O} ⊙skel ac
        = ap (λ coboundary → Ker/Im coboundary cc.augment (snd (cc.cochain 0)))
            (coboundary-first-template-descend-from-two ⊙skel ac)
        where module cc = CochainComplex (cochain-complex ⊙skel ac)
      zeroth-cohomology-group-descend {n = S n} ⊙skel ac
        = ap (λ coboundary → Ker/Im coboundary cc.augment (snd (cc.cochain 0)))
            (coboundary-first-template-descend-from-far ⊙skel ac (ltSR (O<S n)) (<-ap-S (O<S n)))
        where module cc = CochainComplex (cochain-complex ⊙skel ac)

      zeroth-cohomology-group-β : ∀ (⊙skel : ⊙Skeleton {i} 1) ac
        →  cohomology-group (cochain-complex ⊙skel ac) 0
        == Ker/Im
            (TG.cw-co∂-head ⊙skel ac)
            (TAA.cw-coε (⊙cw-init ⊙skel)) (snd (CochainComplex.cochain (cochain-complex ⊙skel ac) 0))
      zeroth-cohomology-group-β ⊙skel ac
        = ap (λ coboundary → Ker/Im coboundary cc.augment (snd (cc.cochain 0)))
            (coboundary-first-template-β ⊙skel ac)
        where module cc = CochainComplex (cochain-complex ⊙skel ac)

  abstract
    zeroth-cohomology-group : ∀ {n} (⊙skel : ⊙Skeleton {i} n) ac
      → C 0 ⊙⟦ ⊙skel ⟧ ≃ᴳ cohomology-group (cochain-complex ⊙skel ac) 0
    zeroth-cohomology-group {n = 0} ⊙skel ac = ZCGD.C-cw-iso-ker/im ⊙skel ac
    zeroth-cohomology-group {n = 1} ⊙skel ac =
          coeᴳ-iso (zeroth-cohomology-group-β ⊙skel ac) ⁻¹ᴳ
      ∘eᴳ ZCG.C-cw-iso-ker/im ⊙skel ac
    zeroth-cohomology-group {n = S (S n)} ⊙skel ac =
          coeᴳ-iso (zeroth-cohomology-group-descend ⊙skel ac) ⁻¹ᴳ
      ∘eᴳ zeroth-cohomology-group (⊙cw-init ⊙skel) (⊙init-has-cells-with-choice ⊙skel ac)
      ∘eᴳ C-cw-descend 0 (pos-≠ (ℕ-O≠S n)) (pos-≠ (ℕ-O≠S (S n))) ⊙skel ac
