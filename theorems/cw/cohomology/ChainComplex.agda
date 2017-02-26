{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cw.CW
open import cw.DegreeBySquashing
open import cohomology.ChainComplex

module cw.cohomology.ChainComplex {i : ULevel} where

  chain-template : ∀ {n} (skel : Skeleton {i} n)
    → (m : ℕ) → Dec (m ≤ n) → AbGroup i
  chain-template skel m (inl m≤n) = FreeAbGroup (cells-nth m≤n skel)
  chain-template skel m (inr _) = Lift-abgroup {j = i} Unit-abgroup

  boundary-nth-template : ∀ {n} (skel : Skeleton {i} n) dec
    → has-degrees-with-finite-supports skel dec
    → (m : ℕ) (m≤n : m ≤ n) (Sm≤n : S m ≤ n)
    → cw-init (cw-take Sm≤n skel) == cw-take (≤-trans lteS Sm≤n) skel
    → cw-take (≤-trans lteS Sm≤n) skel == cw-take m≤n skel
    → (FreeAbGroup.El (cells-nth Sm≤n skel) → FreeAbGroup.El (cells-nth m≤n skel))
  boundary-nth-template skel dec fin-sup m m≤n Sm≤n path₀ path₁ =
      transport (λ lower-skel → FreeAbGroup.El (cells-last lower-skel)) (path₀ ∙ path₁)
    ∘ FormalSum-extend (FreeAbGroup (cells-last (cw-init (cw-take Sm≤n skel))))
        (boundary'-nth Sm≤n skel dec fin-sup)

  abstract
    boundary-pres-comp-nth-template : ∀ {n} (skel : Skeleton {i} n) dec fin-sup m m≤n Sm≤n path₀ path₁
      → preserves-comp (FreeAbGroup.comp (cells-nth Sm≤n skel)) (FreeAbGroup.comp (cells-nth m≤n skel))
          (boundary-nth-template skel dec fin-sup m m≤n Sm≤n path₀ path₁)
    boundary-pres-comp-nth-template skel dec fin-sup m m≤n Sm≤n path₀ path₁ =
      ∘-pres-comp (transportᴳ (λ lower-skel → FreeAbGroup.grp (cells-last lower-skel)) (path₀ ∙ path₁))
        (FreeAbGroup-extend (FreeAbGroup (cells-last (cw-init (cw-take Sm≤n skel))))
          (boundary'-nth Sm≤n skel dec fin-sup))

  boundary-hom-nth-template : ∀ {n} (skel : Skeleton {i} n) dec
    → has-degrees-with-finite-supports skel dec
    → (m : ℕ) (m≤n : m ≤ n) (Sm≤n : S m ≤ n)
    → cw-init (cw-take Sm≤n skel) == cw-take (≤-trans lteS Sm≤n) skel
    → cw-take (≤-trans lteS Sm≤n) skel == cw-take m≤n skel
    → (FreeAbGroup.grp (cells-nth Sm≤n skel) →ᴳ FreeAbGroup.grp (cells-nth m≤n skel))
  boundary-hom-nth-template skel dec fin-sup m m≤n Sm≤n path₀ path₁ = record {
    f = boundary-nth-template skel dec fin-sup m m≤n Sm≤n path₀ path₁;
    pres-comp = boundary-pres-comp-nth-template skel dec fin-sup m m≤n Sm≤n path₀ path₁}

  boundary-hom-template : ∀ {n} (skel : Skeleton {i} n) dec
    → has-degrees-with-finite-supports skel dec
    → (m : ℕ) (m≤n? : Dec (m ≤ n)) (Sm≤n? : Dec (S m ≤ n))
    → (AbGroup.grp (chain-template skel (S m) Sm≤n?) →ᴳ AbGroup.grp (chain-template skel m m≤n?))
  boundary-hom-template skel dec fin-sup m _ (inr _) = cst-hom
  boundary-hom-template skel dec fin-sup m (inr m≰n) (inl Sm≤n) = ⊥-rec $ m≰n (≤-trans lteS Sm≤n)
  boundary-hom-template skel dec fin-sup m (inl m≤n) (inl Sm≤n) =
    boundary-hom-nth-template skel dec fin-sup m m≤n Sm≤n (cw-init-take Sm≤n skel)
      (ap (λ Sm≤n → cw-take Sm≤n skel) (≤-has-all-paths (≤-trans lteS Sm≤n) m≤n))

  chain-complex : ∀ {n} (skel : Skeleton {i} n) dec
    → has-degrees-with-finite-supports skel dec
    → ChainComplex i
  chain-complex {n} skel dec fin-sup = record {M} where
    module M where
      head : AbGroup i
      head = Lift-abgroup {j = i} ℤ-abgroup

      chain : ℕ → AbGroup i
      chain m = chain-template skel m (≤-dec m n)

      augment : AbGroup.grp (chain 0) →ᴳ AbGroup.grp head
      augment = FreeAbGroup-extend head λ _ → lift 1

      boundary : ∀ m → (AbGroup.grp (chain (S m)) →ᴳ AbGroup.grp (chain m))
      boundary m = boundary-hom-template skel dec fin-sup m (≤-dec m n) (≤-dec (S m) n)

  cochain-complex : ∀ {j} {n} (skel : Skeleton {i} n)
    (dec : has-cells-with-dec-eq skel)
    (fin-sup : has-degrees-with-finite-supports skel dec)
    → AbGroup j → CochainComplex (lmax i j)
  cochain-complex skel dec fin-sup G = complex-dualize
    (chain-complex skel dec fin-sup) G
