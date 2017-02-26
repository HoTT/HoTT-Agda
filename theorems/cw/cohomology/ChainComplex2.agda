{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cw.CW
open import cw.DegreeBySquashing
open import cohomology.ChainComplex
open import cw.cohomology.ChainComplex

module cw.cohomology.ChainComplex2 {i : ULevel} where

  abstract
    path-lemma₀ : ∀ {n} (skel : Skeleton {i} (S n)) m (m<n : m < n) (Sm<n : S m < n)
      →  ap (λ m≤Sn → cw-take m≤Sn skel) (≤-has-all-paths (≤-trans lteS (lteSR (inr Sm<n))) (lteSR (inr m<n)))
      == ap (λ m≤n → cw-take m≤n (cw-init skel)) (≤-has-all-paths (≤-trans lteS (inr Sm<n)) (inr m<n))
    path-lemma₀ skel m m<n Sm<n =
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
    test₀ : ∀ {n} (skel : Skeleton {i} (S n)) dec
      → (fin-sup : has-degrees-with-finite-supports skel dec)
      → (m : ℕ) (m<n : m < n) (Sm<n : S m < n)
      → boundary-hom-template {n = S n} skel dec fin-sup m (inl (lteSR (inr m<n))) (inl (lteSR (inr Sm<n)))
        == boundary-hom-template {n = n} (cw-init skel)
          (init-has-cells-with-dec-eq skel dec)
          (init-has-degrees-with-finite-supports skel dec fin-sup)
          m (inl (inr m<n)) (inl (inr Sm<n))
    test₀ skel dec fin-sup m m<n Sm<n = group-hom= $
      ap (boundary-nth-template skel dec fin-sup m (lteSR (inr m<n)) (lteSR (inr Sm<n)) (cw-init-take (lteSR (inr Sm<n)) skel))
        (path-lemma₀ skel m m<n Sm<n)

  abstract
    test₁ : ∀ {n} (skel : Skeleton {i} (S (S n))) dec fin-sup
      → boundary-hom-template {n = S (S n)} skel dec fin-sup n (inl (lteSR lteS)) (inl lteS)
        == boundary-hom-template {n = (S n)} (cw-init skel)
          (init-has-cells-with-dec-eq skel dec)
          (init-has-degrees-with-finite-supports skel dec fin-sup)
          n (inl lteS) (inl lteE)
    test₁ skel dec fin-sup = group-hom= $
      ap (boundary-nth-template skel dec fin-sup _ (lteSR lteS) lteS idp) (path-lemma₁ skel)

  abstract
    test₂ : ∀ {n} (skel : Skeleton {i} (S n)) dec fin-sup
      → boundary-hom-template {n = S n} skel dec fin-sup n (inl lteS) (inl lteE)
        == FreeAbGroup-extend (FreeAbGroup (cells-last (cw-init skel)))
          (boundary'-last skel dec fin-sup)
    test₂ skel dec fin-sup = group-hom= $
      ap (boundary-nth-template skel dec fin-sup _ lteS lteE idp) (path-lemma₂ skel)
