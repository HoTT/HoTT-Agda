{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.ChainComplex
open import cohomology.Theory
open import groups.KernelImage
open import cw.CW

module cw.cohomology.reconstructed.cochain.Complex {i : ULevel} (OT : OrdinaryTheory i) where

  open OrdinaryTheory OT
  open import cw.cohomology.WedgeOfCells OT
  import cw.cohomology.reconstructed.TipAndAugment OT as TAA
  import cw.cohomology.reconstructed.TipCoboundary OT as TC
  import cw.cohomology.reconstructed.HigherCoboundary OT as HC

  cochain-template : ∀ {n} (⊙skel : ⊙Skeleton {i} n) {m}
    → Dec (m ≤ n) → AbGroup i
  cochain-template ⊙skel (inr _) = Lift-abgroup {j = i} Unit-abgroup
  cochain-template ⊙skel {m = 0} (inl 0≤n) = TAA.C2×CX₀-abgroup (⊙cw-take 0≤n ⊙skel) 0
  cochain-template ⊙skel {m = S m} (inl Sm≤n) = CXₙ/Xₙ₋₁-abgroup (⊙cw-take Sm≤n ⊙skel) (ℕ-to-ℤ (S m))

  cochain-is-abelian-template : ∀ {n} (⊙skel : ⊙Skeleton {i} n) {m} m≤n?
    → is-abelian (AbGroup.grp (cochain-template ⊙skel {m} m≤n?))
  cochain-is-abelian-template ⊙skel m≤n? = AbGroup.comm (cochain-template ⊙skel m≤n?)

  abstract
    private
      coboundary-first-template : ∀ {n} (⊙skel : ⊙Skeleton {i} n)
        → (0≤n : 0 ≤ n) (1≤n : 1 ≤ n)
        → ⊙cw-init (⊙cw-take 1≤n ⊙skel) == ⊙cw-take (≤-trans lteS 1≤n) ⊙skel
        → ⊙cw-take (≤-trans lteS 1≤n) ⊙skel == ⊙cw-take 0≤n ⊙skel
        → TAA.C2×CX₀ (⊙cw-take 0≤n ⊙skel) 0 →ᴳ CXₙ/Xₙ₋₁ (⊙cw-take 1≤n ⊙skel) 1
      coboundary-first-template ⊙skel 0≤n 1≤n path₀ path₁ =
           TC.cw-co∂-head (⊙cw-take 1≤n ⊙skel)
        ∘ᴳ transport!ᴳ (λ ⊙skel → TAA.C2×CX₀ ⊙skel 0) (path₀ ∙ path₁)

      coboundary-higher-template : ∀ {n} (⊙skel : ⊙Skeleton {i} n)
        → {m : ℕ} (Sm≤n : S m ≤ n) (SSm≤n : S (S m) ≤ n)
        → ⊙cw-init (⊙cw-take SSm≤n ⊙skel) == ⊙cw-take (≤-trans lteS SSm≤n) ⊙skel
        → ⊙cw-take (≤-trans lteS SSm≤n) ⊙skel == ⊙cw-take Sm≤n ⊙skel
        →  CXₙ/Xₙ₋₁ (⊙cw-take Sm≤n ⊙skel)  (ℕ-to-ℤ (S m))
        →ᴳ CXₙ/Xₙ₋₁ (⊙cw-take SSm≤n ⊙skel) (ℕ-to-ℤ (S (S m)))
      coboundary-higher-template ⊙skel {m} Sm≤n SSm≤n path₀ path₁ =
           HC.cw-co∂-last (⊙cw-take SSm≤n ⊙skel)
        ∘ᴳ transport!ᴳ (λ ⊙skel → CXₙ/Xₙ₋₁ ⊙skel (ℕ-to-ℤ (S m))) (path₀ ∙ path₁)

  coboundary-template : ∀ {n} (⊙skel : ⊙Skeleton {i} n)
    → {m : ℕ} (m≤n? : Dec (m ≤ n)) (Sm≤n? : Dec (S m ≤ n))
    →  AbGroup.grp (cochain-template ⊙skel m≤n?)
    →ᴳ AbGroup.grp (cochain-template ⊙skel Sm≤n?)
  coboundary-template ⊙skel _ (inr _) = cst-hom
  coboundary-template ⊙skel (inr m≰n) (inl Sm≤n) = ⊥-rec $ m≰n (≤-trans lteS Sm≤n)
  coboundary-template ⊙skel {m = 0} (inl 0≤n) (inl 1≤n) =
    coboundary-first-template ⊙skel 0≤n 1≤n (⊙cw-init-take 1≤n ⊙skel)
      (ap (λ 0≤n → ⊙cw-take 0≤n ⊙skel) (≤-has-all-paths (≤-trans lteS 1≤n) 0≤n))
  coboundary-template ⊙skel {m = S m} (inl Sm≤n) (inl SSm≤n) =
    coboundary-higher-template ⊙skel Sm≤n SSm≤n (⊙cw-init-take SSm≤n ⊙skel)
      (ap (λ Sm≤n → ⊙cw-take Sm≤n ⊙skel) (≤-has-all-paths (≤-trans lteS SSm≤n) Sm≤n))

  cochain-complex : ∀ {n} → ⊙Skeleton {i} n → CochainComplex i
  cochain-complex {n} ⊙skel = record {M} where
    module M where
      head : AbGroup i
      head = C-abgroup 0 (⊙Lift ⊙Bool)

      cochain : ℕ → AbGroup i
      cochain m = cochain-template ⊙skel (≤-dec m n)

      augment : C 0 (⊙Lift ⊙Bool) →ᴳ AbGroup.grp (cochain 0)
      augment = TAA.cw-coε (⊙cw-take (O≤ n) ⊙skel)

      coboundary : ∀ m → (AbGroup.grp (cochain m) →ᴳ AbGroup.grp (cochain (S m)))
      coboundary m = coboundary-template ⊙skel (≤-dec m n) (≤-dec (S m) n)

  {- Properties of coboundaries -}

  {- lemmas of paths -}
  private
    abstract
      path-lemma₀ : ∀ {n} (⊙skel : ⊙Skeleton {i} (S n)) {m} (m<n : m < n) (Sm<n : S m < n)
        →  ap (λ m≤Sn → ⊙cw-take m≤Sn ⊙skel) (≤-has-all-paths (≤-trans lteS (lteSR (inr Sm<n))) (lteSR (inr m<n)))
        == ap (λ m≤n → ⊙cw-take m≤n (⊙cw-init ⊙skel)) (≤-has-all-paths (≤-trans lteS (inr Sm<n)) (inr m<n))
      path-lemma₀ ⊙skel m<n Sm<n =
        ap (λ m≤Sn → ⊙cw-take m≤Sn ⊙skel) (≤-has-all-paths (≤-trans lteS (lteSR (inr Sm<n))) (lteSR (inr m<n)))
          =⟨ ap (ap (λ m≤Sn → ⊙cw-take m≤Sn ⊙skel)) (contr-has-all-paths _ _) ⟩
        ap (λ m≤Sn → ⊙cw-take m≤Sn ⊙skel) (ap (lteSR ∘ inr) (<-has-all-paths (<-trans ltS Sm<n) m<n))
          =⟨ ∘-ap (λ m≤Sn → ⊙cw-take m≤Sn ⊙skel) (lteSR ∘ inr) _ ⟩
        ap (λ Sm<n → ⊙cw-take (lteSR (inr Sm<n)) ⊙skel) (<-has-all-paths (<-trans ltS Sm<n) m<n)
          =⟨ ap-∘ (λ m≤n → ⊙cw-take m≤n (⊙cw-init ⊙skel)) inr _ ⟩
        ap (λ m≤n → ⊙cw-take m≤n (⊙cw-init ⊙skel)) (ap inr (<-has-all-paths (<-trans ltS Sm<n) m<n))
          =⟨ ap (ap (λ m≤n → ⊙cw-take m≤n (⊙cw-init ⊙skel))) (contr-has-all-paths _ _) ⟩
        ap (λ m≤n → ⊙cw-take m≤n (⊙cw-init ⊙skel)) (≤-has-all-paths (≤-trans lteS (inr Sm<n)) (inr m<n))
          =∎

      -- would be trivial with [≤-has-all-paths] defined with the set detection (issue #2003)
      path-lemma₁ : ∀ {n} (⊙skel : ⊙Skeleton {i} (S (S n)))
        →  ap (λ n≤SSn → ⊙cw-take n≤SSn ⊙skel) (≤-has-all-paths (lteSR lteS) (lteSR lteS))
        == ap (λ n≤Sn → ⊙cw-take n≤Sn (⊙cw-init ⊙skel)) (≤-has-all-paths lteS lteS)
      path-lemma₁ ⊙skel =
        ap (λ n≤SSn → ⊙cw-take n≤SSn ⊙skel) (≤-has-all-paths (lteSR lteS) (lteSR lteS))
          =⟨ ap (ap (λ n≤SSn → ⊙cw-take n≤SSn ⊙skel)) (contr-has-all-paths _ _) ⟩
        idp
          =⟨ ap (ap (λ n≤Sn → ⊙cw-take n≤Sn (⊙cw-init ⊙skel))) (contr-has-all-paths _ _) ⟩
        ap (λ n≤Sn → ⊙cw-take n≤Sn (⊙cw-init ⊙skel)) (≤-has-all-paths lteS lteS)
          =∎

      -- would be trivial with [≤-has-all-paths] defined with the set detection (issue #2003)
      path-lemma₂ : ∀ {n} (⊙skel : ⊙Skeleton {i} (S n))
        → ap (λ n≤Sn → ⊙cw-take n≤Sn ⊙skel) (≤-has-all-paths lteS lteS) == idp
      path-lemma₂ ⊙skel =
        ap (λ n≤Sn → ⊙cw-take n≤Sn ⊙skel) (≤-has-all-paths lteS lteS)
          =⟨ ap (ap (λ n≤Sn → ⊙cw-take n≤Sn ⊙skel)) (contr-has-all-paths _ _) ⟩
        idp
          =∎

  {- properties of coboundary-template -}
  abstract
    {- lemmas of the first coboundary -}
    coboundary-first-template-descend-from-far : ∀ {n} (⊙skel : ⊙Skeleton {i} (S n)) 0<n 1<n
      → coboundary-template {n = S n} ⊙skel {0} (inl (lteSR (inr 0<n))) (inl (lteSR (inr 1<n)))
        == coboundary-template {n = n} (⊙cw-init ⊙skel) (inl (inr 0<n)) (inl (inr 1<n))
    coboundary-first-template-descend-from-far ⊙skel 0<n 1<n =
      ap (coboundary-first-template ⊙skel (lteSR (inr 0<n)) (lteSR (inr 1<n)) (⊙cw-init-take (lteSR (inr 1<n)) ⊙skel))
        (path-lemma₀ ⊙skel 0<n 1<n)

    coboundary-first-template-descend-from-two : ∀ (⊙skel : ⊙Skeleton {i} 2)
      → coboundary-template {n = 2} ⊙skel (inl (lteSR lteS)) (inl lteS)
        == coboundary-template {n = 1} (⊙cw-init ⊙skel) (inl lteS) (inl lteE)
    coboundary-first-template-descend-from-two ⊙skel =
      ap (coboundary-first-template ⊙skel (lteSR lteS) lteS idp) (path-lemma₁ ⊙skel)

    coboundary-first-template-β : ∀ (⊙skel : ⊙Skeleton {i} 1)
      →  coboundary-template {n = 1} ⊙skel (inl lteS) (inl lteE)
      == TC.cw-co∂-head ⊙skel
    coboundary-first-template-β ⊙skel = group-hom= $
        ap (GroupHom.f ∘ coboundary-first-template ⊙skel lteS lteE idp) (path-lemma₂ ⊙skel)

    {- lemmas of higher coboundaries -}
    coboundary-higher-template-descend-from-far : ∀ {n} (⊙skel : ⊙Skeleton {i} (S n)) {m} Sm<n SSm<n
      → coboundary-template {n = S n} ⊙skel {m = S m} (inl (lteSR (inr Sm<n))) (inl (lteSR (inr SSm<n)))
        == coboundary-template {n = n} (⊙cw-init ⊙skel) {m = S m} (inl (inr Sm<n)) (inl (inr SSm<n))
    coboundary-higher-template-descend-from-far ⊙skel {m} Sm<n SSm<n =
      ap (coboundary-higher-template ⊙skel (lteSR (inr Sm<n)) (lteSR (inr SSm<n)) (⊙cw-init-take (lteSR (inr SSm<n)) ⊙skel))
        (path-lemma₀ ⊙skel Sm<n SSm<n)

    coboundary-higher-template-descend-from-one-above : ∀ {n} (⊙skel : ⊙Skeleton {i} (S (S (S n))))
      → coboundary-template {n = S (S (S n))} ⊙skel {m = S n} (inl (lteSR lteS)) (inl lteS)
        == coboundary-template {n = S (S n)} (⊙cw-init ⊙skel) {m = S n} (inl lteS) (inl lteE)
    coboundary-higher-template-descend-from-one-above ⊙skel =
      ap (coboundary-higher-template ⊙skel (lteSR lteS) lteS idp) (path-lemma₁ ⊙skel)

    coboundary-higher-template-β : ∀ {n} (⊙skel : ⊙Skeleton {i} (S (S n)))
      →  coboundary-template {n = S (S n)} ⊙skel {m = S n} (inl lteS) (inl lteE)
      == HC.cw-co∂-last ⊙skel
    coboundary-higher-template-β ⊙skel = group-hom= $
      ap (GroupHom.f ∘ coboundary-higher-template ⊙skel lteS lteE idp) (path-lemma₂ ⊙skel)
