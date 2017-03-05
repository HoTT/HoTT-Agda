{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cw.CW
open import cw.DegreeBySquashing
open import cohomology.ChainComplex

module cw.cohomology.CellularChainComplex {i : ULevel} where

  chain-template : ∀ {n} (skel : Skeleton {i} n) {m}
    → Dec (m ≤ n) → AbGroup i
  chain-template skel (inl m≤n) = FreeAbGroup (cells-nth m≤n skel)
  chain-template skel (inr _) = Lift-abgroup {j = i} Unit-abgroup

  abstract
    boundary-nth-template : ∀ {n} (skel : Skeleton {i} n) dec
      → has-degrees-with-finite-supports skel dec
      → {m : ℕ} (m≤n : m ≤ n) (Sm≤n : S m ≤ n)
      → cw-init (cw-take Sm≤n skel) == cw-take (≤-trans lteS Sm≤n) skel
      → cw-take (≤-trans lteS Sm≤n) skel == cw-take m≤n skel
      →  FreeAbGroup.grp (cells-nth Sm≤n skel)
      →ᴳ FreeAbGroup.grp (cells-nth m≤n skel)
    boundary-nth-template skel dec fin-sup m≤n Sm≤n path₀ path₁ =
         transportᴳ (λ lower-skel → FreeAbGroup.grp (cells-last lower-skel)) (path₀ ∙ path₁)
      ∘ᴳ FreeAbGroup-extend (FreeAbGroup (cells-last (cw-init (cw-take Sm≤n skel))))
           (boundary'-nth Sm≤n skel dec fin-sup)

  boundary-template : ∀ {n} (skel : Skeleton {i} n) dec
    → has-degrees-with-finite-supports skel dec
    → {m : ℕ} (m≤n? : Dec (m ≤ n)) (Sm≤n? : Dec (S m ≤ n))
    →  AbGroup.grp (chain-template skel Sm≤n?)
    →ᴳ AbGroup.grp (chain-template skel m≤n?)
  boundary-template skel dec fin-sup _ (inr _) = cst-hom
  boundary-template skel dec fin-sup (inr m≰n) (inl Sm≤n) = ⊥-rec $ m≰n (≤-trans lteS Sm≤n)
  boundary-template skel dec fin-sup (inl m≤n) (inl Sm≤n) =
    boundary-nth-template skel dec fin-sup m≤n Sm≤n (cw-init-take Sm≤n skel)
      (ap (λ m≤n → cw-take m≤n skel) (≤-has-all-paths (≤-trans lteS Sm≤n) m≤n))

  chain-complex : ∀ {n} (skel : Skeleton {i} n) dec
    → has-degrees-with-finite-supports skel dec
    → ChainComplex i
  chain-complex {n} skel dec fin-sup = record {M} where
    module M where
      head : AbGroup i
      head = Lift-abgroup {j = i} ℤ-abgroup

      chain : ℕ → AbGroup i
      chain m = chain-template skel (≤-dec m n)

      augment : AbGroup.grp (chain 0) →ᴳ AbGroup.grp head
      augment = FreeAbGroup-extend head λ _ → lift 1

      boundary : ∀ m → (AbGroup.grp (chain (S m)) →ᴳ AbGroup.grp (chain m))
      boundary m = boundary-template skel dec fin-sup (≤-dec m n) (≤-dec (S m) n)

  cochain-complex : ∀ {j} {n} (skel : Skeleton {i} n) dec
    → has-degrees-with-finite-supports skel dec
    → AbGroup j → CochainComplex (lmax i j)
  cochain-complex skel dec fin-sup G = complex-dualize
    (chain-complex skel dec fin-sup) G

  {- properties of coboundaries -}

  abstract
    private
      path-lemma₀ : ∀ {n} (skel : Skeleton {i} (S n)) {m} (m<n : m < n) (Sm<n : S m < n)
        →  ap (λ m≤Sn → cw-take m≤Sn skel) (≤-has-all-paths (≤-trans lteS (lteSR (inr Sm<n))) (lteSR (inr m<n)))
        == ap (λ m≤n → cw-take m≤n (cw-init skel)) (≤-has-all-paths (≤-trans lteS (inr Sm<n)) (inr m<n))
      path-lemma₀ skel m<n Sm<n =
        ap (λ m≤Sn → cw-take m≤Sn skel) (≤-has-all-paths (≤-trans lteS (lteSR (inr Sm<n))) (lteSR (inr m<n)))
          =⟨ ap (ap (λ m≤Sn → cw-take m≤Sn skel)) (contr-has-all-paths (≤-is-prop _ _) _ _) ⟩
        ap (λ m≤Sn → cw-take m≤Sn skel) (ap (lteSR ∘ inr) (<-has-all-paths (<-trans ltS Sm<n) m<n))
          =⟨ ∘-ap (λ m≤Sn → cw-take m≤Sn skel) (lteSR ∘ inr) _ ⟩
        ap (λ Sm<n → cw-take (lteSR (inr Sm<n)) skel) (<-has-all-paths (<-trans ltS Sm<n) m<n)
          =⟨ ap-∘ (λ m≤n → cw-take m≤n (cw-init skel)) inr _ ⟩
        ap (λ m≤n → cw-take m≤n (cw-init skel)) (ap inr (<-has-all-paths (<-trans ltS Sm<n) m<n))
          =⟨ ap (ap (λ m≤n → cw-take m≤n (cw-init skel))) (contr-has-all-paths (≤-is-prop _ _) _ _) ⟩
        ap (λ m≤n → cw-take m≤n (cw-init skel)) (≤-has-all-paths (≤-trans lteS (inr Sm<n)) (inr m<n))
          =∎

      path-lemma₁ : ∀ {n} (skel : Skeleton {i} (S (S n)))
        →  ap (λ n≤SSn → cw-take n≤SSn skel) (≤-has-all-paths (lteSR lteS) (lteSR lteS))
        == ap (λ n≤Sn → cw-take n≤Sn (cw-init skel)) (≤-has-all-paths lteS lteS)
      path-lemma₁ skel =
        ap (λ n≤SSn → cw-take n≤SSn skel) (≤-has-all-paths (lteSR lteS) (lteSR lteS))
          =⟨ ap (ap (λ n≤SSn → cw-take n≤SSn skel)) (contr-has-all-paths (≤-is-prop _ _) _ _) ⟩
        idp
          =⟨ ap (ap (λ n≤Sn → cw-take n≤Sn (cw-init skel))) (contr-has-all-paths (≤-is-prop _ _) _ _) ⟩
        ap (λ n≤Sn → cw-take n≤Sn (cw-init skel)) (≤-has-all-paths lteS lteS)
          =∎

      path-lemma₂ : ∀ {n} (skel : Skeleton {i} (S n))
        → ap (λ n≤Sn → cw-take n≤Sn skel) (≤-has-all-paths lteS lteS) == idp
      path-lemma₂ skel =
        ap (λ n≤Sn → cw-take n≤Sn skel) (≤-has-all-paths lteS lteS)
          =⟨ ap (ap (λ n≤Sn → cw-take n≤Sn skel)) (contr-has-all-paths (≤-is-prop _ _) _ _) ⟩
        idp
          =∎

  abstract
    boundary-template-descend-from-far : ∀ {n} (skel : Skeleton {i} (S n)) dec fin-sup {m} m<n Sm<n
      → boundary-template {n = S n} skel dec fin-sup {m} (inl (lteSR (inr m<n))) (inl (lteSR (inr Sm<n)))
        == boundary-template {n = n} (cw-init skel)
          (init-has-cells-with-dec-eq skel dec)
          (init-has-degrees-with-finite-supports skel dec fin-sup)
          (inl (inr m<n)) (inl (inr Sm<n))
    boundary-template-descend-from-far skel dec fin-sup m<n Sm<n =
      ap (boundary-nth-template skel dec fin-sup (lteSR (inr m<n)) (lteSR (inr Sm<n)) (cw-init-take (lteSR (inr Sm<n)) skel))
        (path-lemma₀ skel m<n Sm<n)

    boundary-template-descend-from-two-above : ∀ {n} (skel : Skeleton {i} (S (S n))) dec fin-sup
      → boundary-template {n = S (S n)} skel dec fin-sup (inl (lteSR lteS)) (inl lteS)
        == boundary-template {n = (S n)} (cw-init skel)
          (init-has-cells-with-dec-eq skel dec)
          (init-has-degrees-with-finite-supports skel dec fin-sup)
          (inl lteS) (inl lteE)
    boundary-template-descend-from-two-above skel dec fin-sup =
      ap (boundary-nth-template skel dec fin-sup (lteSR lteS) lteS idp) (path-lemma₁ skel)

    boundary-template-β : ∀ {n} (skel : Skeleton {i} (S n)) dec fin-sup
      →  boundary-template {n = S n} skel dec fin-sup (inl lteS) (inl lteE)
      == FreeAbGroup-extend
            (FreeAbGroup (cells-last (cw-init skel)))
            (boundary'-last skel dec fin-sup)
    boundary-template-β skel dec fin-sup = group-hom= $
      ap (GroupHom.f ∘ boundary-nth-template skel dec fin-sup lteS lteE idp) (path-lemma₂ skel)
