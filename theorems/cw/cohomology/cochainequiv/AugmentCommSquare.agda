{-# OPTIONS --without-K --rewriting #-}

open import HoTT renaming (pt to ⊙pt)
open import cw.CW
open import cw.FinCW
open import cohomology.Theory
open import groups.Int
open import groups.DisjointlyPointedSet

module cw.cohomology.cochainequiv.AugmentCommSquare (OT : OrdinaryTheory lzero)
  (⊙fin-skel : ⊙FinSkeleton 0) where

open OrdinaryTheory OT
open import cw.cohomology.reconstructed.TipAndAugment OT ⊙⦉ ⊙fin-skel ⦊

private
  I = ⊙FinSkeleton.skel ⊙fin-skel
  ac = ⊙FinSkeleton-has-cells-with-choice 0 ⊙fin-skel lzero
  pt = ⊙FinSkeleton.skel ⊙fin-skel

abstract
  augment-comm-sqr :
    CommSquareEquiv
      (GroupHom.f cw-coε)
      (_∘ᴳ FreeAbGroup-extend (Lift-abgroup {j = lzero} ℤ-abgroup) λ _ → lift 1)
      ((_∘ᴳ lower-hom {j = lzero}) ∘ <– (ℤ→ᴳ-equiv-idf (C2 0)))
      (FreeAbGroup-extend (C2-abgroup 0) ∘ GroupIso.f (C2×CX₀-diag-β ac))
  augment-comm-sqr = comm-sqr (λ g → equiv-adj'
    (GroupIso.f-equiv (FreeAbGroup-extend-iso (C2-abgroup 0) ∘eᴳ C2×CX₀-diag-β ac))
    (! $ pair×= idp
      ( ap (GroupIso.g (CX₀-diag-β ac)) (λ= λ _ → Group.inv-r (C2 0) g)
      ∙ GroupHom.pres-ident (GroupIso.g-hom (CX₀-diag-β ac))))) ,
    (GroupIso.f-is-equiv (pre∘ᴳ-iso (C2-abgroup 0) (lower-iso {j = lzero}) ∘eᴳ ℤ→ᴳ-iso-idf (C2-abgroup 0) ⁻¹ᴳ)) ,
    (GroupIso.f-is-equiv (FreeAbGroup-extend-iso (C2-abgroup 0) ∘eᴳ C2×CX₀-diag-β ac))

  augment-comm-sqrᴳ :
    CommSquareEquivᴳ
      cw-coε
      (pre∘ᴳ-hom (C2-abgroup 0) (FreeAbGroup-extend (Lift-abgroup {j = lzero} ℤ-abgroup) λ _ → lift 1))
      (pre∘ᴳ-hom (C2-abgroup 0) (lower-hom {j = lzero}) ∘ᴳ GroupIso.g-hom (ℤ→ᴳ-iso-idf (C2-abgroup 0)))
      (FreeAbGroup-extend-hom (C2-abgroup 0) ∘ᴳ GroupIso.f-hom (C2×CX₀-diag-β ac))
  augment-comm-sqrᴳ =
    comm-sqrᴳ (fst augment-comm-sqr □$_) , snd augment-comm-sqr
