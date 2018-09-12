{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cw.CW
open import cw.FinCW
open import cw.FinBoundary
open import cohomology.Theory

module cw.cohomology.cochainequiv.FirstCoboundaryCommSquare (OT : OrdinaryTheory lzero)
  (⊙fin-skel : ⊙FinSkeleton 1) where

open OrdinaryTheory OT
open import cw.cohomology.WedgeOfCells OT ⊙⦉ ⊙fin-skel ⦊
open import cw.cohomology.reconstructed.TipAndAugment OT ⊙⦉ ⊙fcw-init ⊙fin-skel ⦊
open import cw.cohomology.reconstructed.TipCoboundary OT ⊙⦉ ⊙fin-skel ⦊
open import cw.cohomology.cochainequiv.DualizedFirstBoundary OT ⊙fin-skel
open import cw.cohomology.cochainequiv.FirstCoboundary OT ⊙fin-skel
open FreeAbelianGroup

private
  fin-skel = ⊙FinSkeleton.skel ⊙fin-skel
  I = AttachedFinSkeleton.numCells fin-skel
  ac = ⊙FinSkeleton-has-cells-with-choice 0 ⊙fin-skel lzero

  ⊙fin-skel₋₁ = ⊙fcw-init ⊙fin-skel
  fin-skel₋₁ = ⊙FinSkeleton.skel ⊙fin-skel₋₁
  ac₋₁ = ⊙FinSkeleton-has-cells-with-choice 0 ⊙fin-skel₋₁ lzero

abstract
  rephrase-dualized-first-boundary-comm-sqr :
    CommSquareEquiv
      (λ g <I → Group.sum (C2 0) (λ <I₋₁ → Group.exp (C2 0) (g <I₋₁) (fdegree-last fin-skel <I <I₋₁)))
      (_∘ᴳ fboundary-last fin-skel)
      (Freeness.extend _ (C2-abgroup 0))
      (Freeness.extend _ (C2-abgroup 0))
  rephrase-dualized-first-boundary-comm-sqr =
    comm-sqr (λ g →
      equiv-adj'
        (GroupIso.f-equiv (Freeness.extend-iso _ (C2-abgroup 0)))
        (λ= λ <I → ! (rephrase-dualized-first-boundary-in-degree g <I))) ,
    Freeness.extend-is-equiv _ (C2-abgroup 0) ,
    Freeness.extend-is-equiv _ (C2-abgroup 0)

  rephrase-cw-co∂-head-comm-sqr :
    CommSquareEquiv
      (λ g <I → Group.sum (C2 0) (λ <I' → Group.exp (C2 0) (g <I') (fdegree-last fin-skel <I <I')))
      (GroupHom.f cw-co∂-head)
      (GroupIso.g (C2×CX₀-diag-β ac₋₁))
      (GroupIso.g (CXₙ/Xₙ₋₁-diag-β ac))
  rephrase-cw-co∂-head-comm-sqr =
    comm-sqr (λ g →
      equiv-adj'
        (GroupIso.g-equiv (CXₙ/Xₙ₋₁-diag-β ac))
        (λ= λ <I → ! (rephrase-cw-co∂-head-in-degree g <I))) ,
    (GroupIso.g-is-equiv (C2×CX₀-diag-β ac₋₁)) ,
    (GroupIso.g-is-equiv (CXₙ/Xₙ₋₁-diag-β ac))

  first-coboundary-comm-sqr :
    CommSquareEquiv
      (GroupHom.f cw-co∂-head)
      (_∘ᴳ fboundary-last fin-skel)
      (Freeness.extend _ (C2-abgroup 0) ∘ GroupIso.f (C2×CX₀-diag-β ac₋₁))
      (Freeness.extend _ (C2-abgroup 0) ∘ GroupIso.f (CXₙ/Xₙ₋₁-diag-β ac))
  first-coboundary-comm-sqr =
    CommSquareEquiv-∘v
      rephrase-dualized-first-boundary-comm-sqr
      (CommSquareEquiv-inverse-v rephrase-cw-co∂-head-comm-sqr)

  first-coboundary-comm-sqrᴳ :
    CommSquareEquivᴳ
      cw-co∂-head
      (pre∘ᴳ-hom (C2-abgroup 0) (fboundary-last fin-skel))
      (Freeness.extend-hom _ (C2-abgroup 0) ∘ᴳ GroupIso.f-hom (C2×CX₀-diag-β ac₋₁))
      (Freeness.extend-hom _ (C2-abgroup 0) ∘ᴳ GroupIso.f-hom (CXₙ/Xₙ₋₁-diag-β ac))
  first-coboundary-comm-sqrᴳ =
    comm-sqrᴳ (fst first-coboundary-comm-sqr □$_) , snd first-coboundary-comm-sqr
