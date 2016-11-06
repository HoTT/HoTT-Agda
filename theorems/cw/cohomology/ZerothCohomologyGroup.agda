{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Theory
open import cohomology.PtdMapSequence
open import groups.ExactSequence
open import groups.Exactness
open import groups.HomSequence
open import groups.PropQuotOfInl
import homotopy.ConstantToSetExtendsToProp as ConstExt

open import cw.CW

module cw.cohomology.ZerothCohomologyGroup {i} (OT : OrdinaryTheory i)
  (⊙skel : ⊙Skeleton {i} 1) (ac : ⊙has-cells-with-choice 0 ⊙skel i) where

open OrdinaryTheory OT
open import cohomology.LongExactSequence
  cohomology-theory 0 (⊙cw-incl-last ⊙skel)
open import cw.cohomology.TipGrid OT ⊙skel ac
open import cw.cohomology.WedgeOfCells OT

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

  G-is-abelian : is-abelian G
  G-is-abelian = C-is-abelian 0 (⊙Lift ⊙Bool)

  C-X₀ : Group i
  C-X₀ = C 0 ⊙⟦ ⊙cw-init ⊙skel ⟧

  C-X₀-is-abelian : is-abelian C-X₀
  C-X₀-is-abelian = C-is-abelian 0 ⊙⟦ ⊙cw-init ⊙skel ⟧

  G-×-C-X₀-is-abelian : is-abelian (G ×ᴳ C-X₀)
  G-×-C-X₀-is-abelian = ×ᴳ-is-abelian G C-X₀ G-is-abelian C-X₀-is-abelian

cw-coε : G →ᴳ G ×ᴳ C-X₀
cw-coε = ×ᴳ-inl {G = G} {H = C-X₀}

module CokerCoε = Coker G-×-C-X₀-is-abelian cw-coε

C-cw-iso-ker/im : C 0 ⊙⟦ ⊙skel ⟧ ≃ᴳ QuotGroup (quot-of-sub (ker-propᴳ cw-co∂-head) CokerCoε.npropᴳ)
C-cw-iso-ker/im = Ker-inl-quot-Im-φ-snd G G-is-abelian C-X₀-is-abelian cw-co∂-head'
              ∘eᴳ Ker-cw-co∂-head'
