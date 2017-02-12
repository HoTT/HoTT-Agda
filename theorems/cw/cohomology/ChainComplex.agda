{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cw.CW
open import cw.DegreeBySquashing
open import cohomology.ChainComplex

module cw.cohomology.ChainComplex {i : ULevel} where

  chain-complex : ∀ {n} (skel : Skeleton {i} n) dec
    → has-degrees-with-finite-supports skel dec
    → ChainComplex i
  chain-complex {n} skel dec fin-sup = record {M} where
    module M where
      head : AbGroup i
      head = Lift-abgroup {j = i} ℤ-abgroup

      chain : ℕ → AbGroup i
      chain m with ≤-dec m n
      chain m | (inl m≤n) = FreeAbGroup (cells-nth m≤n skel)
      chain m | (inr _) = Lift-abgroup {j = i} Unit-abgroup

      augment : AbGroup.grp (chain 0) →ᴳ AbGroup.grp head
      augment = FreeAbGroup-extend head λ _ → lift 1

      boundary : ∀ n → (AbGroup.grp (chain (S n)) →ᴳ AbGroup.grp (chain n))
      boundary m with ≤-dec m n | ≤-dec (S m) n
      boundary m | _         | (inr _) = cst-hom
      boundary m | (inr m≰n) | (inl Sm≤n) = ⊥-rec $ m≰n (≤-trans (inr ltS) Sm≤n)
      boundary m | (inl m≤n) | (inl Sm≤n) =
        GroupIso.f-hom (transportᴳ-iso
          (λ lower-skel → (FreeAbGroup.grp (cells-last lower-skel)))
          (cw-take-take (inr ltS) Sm≤n m≤n skel))
        ∘ᴳ
        FreeAbGroup-extend (FreeAbGroup (cells-last (cw-init (cw-take Sm≤n skel))))
          (boundary'-nth Sm≤n skel dec fin-sup)

  cochain-complex : ∀ {j} {n} (skel : Skeleton {i} n)
    (dec : has-cells-with-dec-eq skel)
    (fin-sup : has-degrees-with-finite-supports skel dec)
    → AbGroup j → CochainComplex (lmax i j)
  cochain-complex skel dec fin-sup G = complex-dualize
    (chain-complex skel dec fin-sup) G
