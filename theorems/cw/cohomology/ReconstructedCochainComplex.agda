{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.ChainComplex
open import cohomology.Theory
open import cw.CW

module cw.cohomology.ReconstructedCochainComplex {i : ULevel} (OT : OrdinaryTheory i) where

  open OrdinaryTheory OT
  import cw.cohomology.CoboundaryGrid OT as CG
  import cw.cohomology.TipAndAugment OT as TAA
  import cw.cohomology.TipGrid OT as TG

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
