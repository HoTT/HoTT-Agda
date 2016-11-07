{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Theory
open import groups.PropQuotOfInl

open import cw.CW

module cw.cohomology.ZerothCohomologyGroup {i} (OT : OrdinaryTheory i)
  (⊙skel : ⊙Skeleton {i} 1) (ac : ⊙has-cells-with-choice 0 ⊙skel i) where

open OrdinaryTheory OT
open import cw.cohomology.TipGrid OT ⊙skel ac

{-

    C(X₀)<------C(X₁) = C(X)
                  ^
                  |
                  |
               C(X₁/X₀)
                 WoC

    WoC := Wedges of Cells
-}

private
  G : Group i
  G = C 0 (⊙Lift ⊙Bool)

  C-X₀ : Group i
  C-X₀ = C 0 ⊙⟦ ⊙cw-init ⊙skel ⟧

  abstract
    G-×-C-X₀-is-abelian : is-abelian (G ×ᴳ C-X₀)
    G-×-C-X₀-is-abelian = ×ᴳ-is-abelian G C-X₀
      (C-is-abelian 0 (⊙Lift ⊙Bool))
      (C-is-abelian 0 ⊙⟦ ⊙cw-init ⊙skel ⟧)

cw-coε : G →ᴳ G ×ᴳ C-X₀
cw-coε = ×ᴳ-inl {G = G} {H = C-X₀}

module CokerCoε = Coker cw-coε G-×-C-X₀-is-abelian

private
  lemma₁ : Ker.grp cw-co∂-head'
    ≃ᴳ QuotGroup (quot-of-sub (ker-propᴳ (cw-co∂-head' ∘ᴳ ×ᴳ-snd {G = G} {H = C-X₀})) (im-npropᴳ cw-coε G-×-C-X₀-is-abelian))
  lemma₁ = Ker-inl-quot-Im-φ-snd G {H = C-X₀} {K = C 1 (⊙Cofiber (⊙cw-incl-last ⊙skel))} G-×-C-X₀-is-abelian cw-co∂-head'

C-cw-iso-ker/im : C 0 ⊙⟦ ⊙skel ⟧
  ≃ᴳ QuotGroup (quot-of-sub (ker-propᴳ cw-co∂-head) (im-npropᴳ cw-coε G-×-C-X₀-is-abelian))
C-cw-iso-ker/im = lemma₁ ∘eᴳ Ker-cw-co∂-head'
