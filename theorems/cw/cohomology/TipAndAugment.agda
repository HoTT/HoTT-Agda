{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory

open import cw.CW

module cw.cohomology.TipAndAugment {i} (OT : OrdinaryTheory i)
  (⊙skel : ⊙Skeleton {i} 0) where

open OrdinaryTheory OT
open import homotopy.DisjointlyPointedSet
open import cohomology.DisjointlyPointedSet OT

module _ (m : ℤ) where
  CX₀ : Group i
  CX₀ = C m (⊙cw-head ⊙skel)

  CX₀-is-abelian : is-abelian CX₀
  CX₀-is-abelian = C-is-abelian m (⊙cw-head ⊙skel)

  C2×CX₀ : Group i
  C2×CX₀ = C2 m ×ᴳ CX₀

  abstract
    C2×CX₀-is-abelian : is-abelian C2×CX₀
    C2×CX₀-is-abelian = ×ᴳ-is-abelian (C2 m) CX₀ (C2-is-abelian m) CX₀-is-abelian

  C2×CX₀-abgroup : AbGroup i
  C2×CX₀-abgroup = C2×CX₀ , C2×CX₀-is-abelian

  CX₀-β : ⊙has-cells-with-choice 0 ⊙skel i
    → CX₀ ≃ᴳ Πᴳ (MinusPoint (⊙cw-head ⊙skel)) (λ _ → C2 m)
  CX₀-β ac = C-set m (⊙cw-head ⊙skel) (snd (⊙Skeleton.skel ⊙skel)) (⊙Skeleton.pt-dec ⊙skel) ac

abstract
  CX₀-≠-is-trivial : ∀ {m} (m≠0 : m ≠ 0)
    → ⊙has-cells-with-choice 0 ⊙skel i
    → is-trivialᴳ (CX₀ m)
  CX₀-≠-is-trivial {m} m≠0 ac =
    iso-preserves'-trivial (CX₀-β m ac) $
      Πᴳ-is-trivial (MinusPoint (⊙cw-head ⊙skel))
        (λ _ → C2 m) (λ _ → C-dimension m≠0)

cw-coε : C2 0 →ᴳ C2×CX₀ 0
cw-coε = ×ᴳ-inl {G = C2 0} {H = CX₀ 0}
