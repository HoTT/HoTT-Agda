{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory

open import cw.CW

module cw.cohomology.ZerothCohomologyGroup {i} (OT : OrdinaryTheory i)
  (⊙skel : ⊙Skeleton {i} 1) (ac : ⊙has-cells-with-choice 0 ⊙skel i) where

open OrdinaryTheory OT
open import cw.cohomology.TipAndAugment OT (⊙cw-init ⊙skel)
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

open import groups.PropQuotOfInl G {H = CX₀}
  {K = C 1 (⊙Cofiber (⊙cw-incl-last ⊙skel))}
  G×CX₀-is-abelian
  cw-co∂-head' cw-co∂-head (λ _ → idp)

module CokerCoε = Coker cw-coε G×CX₀-is-abelian

private
  -- lemmas trying to direct (and speed up) Agda's type checking
  abstract
    lemma₀ : Ker/Im.npropᴳ
      == quot-of-sub (ker-propᴳ cw-co∂-head) (im-npropᴳ cw-coε G×CX₀-is-abelian)
    lemma₀ = idp

    lemma₁ : QuotGroup Ker/Im.npropᴳ
      == QuotGroup (quot-of-sub (ker-propᴳ cw-co∂-head) (im-npropᴳ cw-coε G×CX₀-is-abelian))
    lemma₁ = ap QuotGroup lemma₀

    lemma₂ : Ker/Im.grp == QuotGroup Ker/Im.npropᴳ
    lemma₂ = idp

    lemma₃ : Ker.grp cw-co∂-head'
      ≃ᴳ QuotGroup (quot-of-sub (ker-propᴳ cw-co∂-head) (im-npropᴳ cw-coε G×CX₀-is-abelian))
    lemma₃ = coeᴳ-iso (lemma₂ ∙ lemma₁) ∘eᴳ Ker-inl-quot-Im-φ-snd

C-cw-iso-ker/im : C 0 ⊙⟦ ⊙skel ⟧
  ≃ᴳ QuotGroup (quot-of-sub (ker-propᴳ cw-co∂-head) (im-npropᴳ cw-coε G×CX₀-is-abelian))
C-cw-iso-ker/im = lemma₃ ∘eᴳ Ker-cw-co∂-head'
