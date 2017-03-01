{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import groups.Cokernel
open import cohomology.Theory

open import cw.CW

module cw.cohomology.HigherCoboundary {i} (OT : OrdinaryTheory i)
  {n} (⊙skel : ⊙Skeleton {i} (S (S n))) where

open OrdinaryTheory OT
open import cw.cohomology.WedgeOfCells OT
open import cw.cohomology.GridLongExactSequence cohomology-theory
  (ℕ-to-ℤ (S n)) (⊙cw-incl-last (⊙cw-init ⊙skel)) (⊙cw-incl-last ⊙skel)

cw-co∂-last : CXₙ/Xₙ₋₁ (⊙cw-init ⊙skel) →ᴳ CXₙ/Xₙ₋₁ ⊙skel
cw-co∂-last = grid-co∂

module CokerCo∂ where
  grp = Coker cw-co∂-last (CXₙ/Xₙ₋₁-is-abelian ⊙skel)
  open Group grp public

CokerCo∂ = CokerCo∂.grp
