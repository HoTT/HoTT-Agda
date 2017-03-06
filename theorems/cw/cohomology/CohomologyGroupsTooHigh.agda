{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory

open import cw.CW

module cw.cohomology.CohomologyGroupsTooHigh {i} (OT : OrdinaryTheory i)
  m {n} (n<m : n < m) (G : Group i) (⊙skel : ⊙Skeleton {i} n)
  (ac : ⊙has-cells-with-choice 0 ⊙skel i) where

open OrdinaryTheory OT
open import cw.cohomology.Descending OT

open import groups.KernelImage {G = G}
  {H = Lift-group {j = i} Unit-group}
  {K = Lift-group {j = i} Unit-group}
  cst-hom cst-hom
  (snd (Lift-abgroup Unit-abgroup))
open import groups.KernelCstImageCst G
  (Lift-group {j = i} Unit-group)
  (Lift-group {j = i} Unit-group)
  (snd (Lift-abgroup Unit-abgroup))

C-cw-iso-ker/im : C (ℕ-to-ℤ m) ⊙⟦ ⊙skel ⟧ ≃ᴳ Ker/Im
C-cw-iso-ker/im = Ker-cst-quot-Im-cst ⁻¹ᴳ ∘eᴳ lift-iso
  ∘eᴳ trivial-iso-0ᴳ (C-cw-at-higher ⊙skel n<m ac)
