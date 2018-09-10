{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cw.CW
open import cw.FinCW
open import cw.FinBoundary
open import cohomology.Theory

module cw.cohomology.cochainequiv.HigherCoboundaryCommSquare (OT : OrdinaryTheory lzero)
  {n} (⊙fin-skel : ⊙FinSkeleton (S (S n))) where

open OrdinaryTheory OT
open import cw.cohomology.WedgeOfCells OT
open import cw.cohomology.reconstructed.HigherCoboundary OT ⊙⦉ ⊙fin-skel ⦊
open import cw.cohomology.cochainequiv.DualizedHigherBoundary OT ⊙fin-skel
open import cw.cohomology.cochainequiv.HigherCoboundary OT ⊙fin-skel

private
  fin-skel = ⊙FinSkeleton.skel ⊙fin-skel
  I = AttachedFinSkeleton.numCells fin-skel
  ac = ⊙FinSkeleton-has-cells-with-choice 0 ⊙fin-skel lzero

  ⊙fin-skel₋₁ = ⊙fcw-init ⊙fin-skel
  fin-skel₋₁ = ⊙FinSkeleton.skel ⊙fin-skel₋₁
  ac₋₁ = ⊙FinSkeleton-has-cells-with-choice 0 ⊙fin-skel₋₁ lzero

open FreeAbelianGroup

abstract
  rephrase-dualized-higher-boundary-comm-sqr :
    CommSquareEquiv
      (λ g <I → Group.sum (C2 0) (λ <I₋₁ → Group.exp (C2 0) (g <I₋₁) (fdegree-last fin-skel <I <I₋₁)))
      (_∘ᴳ fboundary-last fin-skel)
      (Freeness.extend _ (C2-abgroup 0))
      (Freeness.extend _ (C2-abgroup 0))
  rephrase-dualized-higher-boundary-comm-sqr =
    comm-sqr (λ g →
      equiv-adj'
        (GroupIso.f-equiv (Freeness.extend-iso _ (C2-abgroup 0)))
        (λ= λ <I → ! (rephrase-dualized-higher-boundary-in-degree g <I))) ,
    Freeness.extend-is-equiv _ (C2-abgroup 0) ,
    Freeness.extend-is-equiv _ (C2-abgroup 0)

  rephrase-cw-co∂-last-comm-sqr :
    CommSquareEquiv
      (λ g <I → Group.sum (C2 0) (λ <I₋₁ → Group.exp (C2 0) (g <I₋₁) (fdegree-last fin-skel <I <I₋₁)))
      (GroupHom.f cw-co∂-last)
      (GroupIso.g (CXₙ/Xₙ₋₁-diag-β ⊙⦉ ⊙fin-skel₋₁ ⦊ ac₋₁))
      (GroupIso.g (CXₙ/Xₙ₋₁-diag-β ⊙⦉ ⊙fin-skel ⦊ ac))
  rephrase-cw-co∂-last-comm-sqr =
    comm-sqr (λ g →
      equiv-adj'
        (GroupIso.g-equiv (CXₙ/Xₙ₋₁-diag-β ⊙⦉ ⊙fin-skel ⦊ ac))
        (λ= λ <I → ! (rephrase-cw-co∂-last-in-degree g <I))) ,
    (GroupIso.g-is-equiv (CXₙ/Xₙ₋₁-diag-β ⊙⦉ ⊙fin-skel₋₁ ⦊ ac₋₁)) ,
    (GroupIso.g-is-equiv (CXₙ/Xₙ₋₁-diag-β ⊙⦉ ⊙fin-skel ⦊ ac))

  higher-coboundary-comm-sqr :
    CommSquareEquiv
      (GroupHom.f cw-co∂-last)
      (_∘ᴳ fboundary-last fin-skel)
      (Freeness.extend _ (C2-abgroup 0) ∘ GroupIso.f (CXₙ/Xₙ₋₁-diag-β ⊙⦉ ⊙fin-skel₋₁ ⦊ ac₋₁))
      (Freeness.extend _ (C2-abgroup 0) ∘ GroupIso.f (CXₙ/Xₙ₋₁-diag-β ⊙⦉ ⊙fin-skel ⦊ ac))
  higher-coboundary-comm-sqr =
    CommSquareEquiv-∘v
      rephrase-dualized-higher-boundary-comm-sqr
      (CommSquareEquiv-inverse-v rephrase-cw-co∂-last-comm-sqr)

  higher-coboundary-comm-sqrᴳ :
    CommSquareEquivᴳ
      cw-co∂-last
      (pre∘ᴳ-hom (C2-abgroup 0) (fboundary-last fin-skel))
      (Freeness.extend-hom _ (C2-abgroup 0) ∘ᴳ GroupIso.f-hom (CXₙ/Xₙ₋₁-diag-β ⊙⦉ ⊙fin-skel₋₁ ⦊ ac₋₁))
      (Freeness.extend-hom _ (C2-abgroup 0) ∘ᴳ GroupIso.f-hom (CXₙ/Xₙ₋₁-diag-β ⊙⦉ ⊙fin-skel ⦊ ac))
  higher-coboundary-comm-sqrᴳ =
    comm-sqrᴳ (fst higher-coboundary-comm-sqr □$_) , snd higher-coboundary-comm-sqr
