{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import groups.Cokernel
open import cohomology.Theory

open import cw.CW

module cw.cohomology.HigherCoboundary {i} (OT : OrdinaryTheory i)
  {n} (⊙skel : ⊙Skeleton {i} (S (S n))) where

open OrdinaryTheory OT
open import cw.WedgeOfCells
open import cw.cohomology.WedgeOfCells OT
open import cw.cohomology.GridLongExactSequence cohomology-theory
  (ℕ-to-ℤ (S n)) (⊙cw-incl-last (⊙cw-init ⊙skel)) (⊙cw-incl-last ⊙skel)

cw-co∂-last : CXₙ/Xₙ₋₁ (⊙cw-init ⊙skel) (ℕ-to-ℤ (S n)) →ᴳ CXₙ/Xₙ₋₁ ⊙skel (ℕ-to-ℤ (S (S n)))
cw-co∂-last = grid-co∂

cw-∂-before-Susp : Xₙ/Xₙ₋₁ (⊙Skeleton.skel ⊙skel) → Susp (Xₙ/Xₙ₋₁ (cw-init (⊙Skeleton.skel ⊙skel)))
cw-∂-before-Susp = grid-∂-before-Susp

⊙cw-∂-before-Susp : ⊙Xₙ/Xₙ₋₁ (⊙Skeleton.skel ⊙skel) ⊙→ ⊙Susp (⊙Xₙ/Xₙ₋₁ (cw-init (⊙Skeleton.skel ⊙skel)))
⊙cw-∂-before-Susp = ⊙grid-∂-before-Susp

cw-∂-before-Susp-glue-β = grid-∂-before-Susp-glue-β
cw-co∂-last-β = grid-co∂-β

module CokerCo∂ where
  grp = Coker cw-co∂-last (CXₙ/Xₙ₋₁-is-abelian ⊙skel (ℕ-to-ℤ (S (S n))))
  open Group grp public

CokerCo∂ = CokerCo∂.grp
