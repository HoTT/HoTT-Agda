{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Theory
open import groups.Exactness
open import groups.HomSequence
open import groups.ExactSequence

open import cw.CW

module cw.cohomology.CoboundaryGrid {i} (OT : OrdinaryTheory i) where

open OrdinaryTheory OT
open import cw.cohomology.Descending OT
open import cw.cohomology.WedgeOfCells OT
import cw.cohomology.GridLongExactSequence

module _ {n} (⊙skel : ⊙Skeleton {i} (S (S n)))
  (ac : ⊙has-cells-with-choice 0 ⊙skel i) where

  private
    n≤SSn : n ≤ S (S n)
    n≤SSn = inr (ltSR ltS)

    module GLES n = cw.cohomology.GridLongExactSequence
      cohomology-theory n (⊙cw-incl-last (⊙cw-init ⊙skel)) (⊙cw-incl-last ⊙skel)

  cw-co∂ : C (ℕ-to-ℤ (S n)) (⊙Cofiber (⊙cw-incl-last (⊙cw-init ⊙skel)))
        →ᴳ C (ℕ-to-ℤ (S (S n))) (⊙Cofiber (⊙cw-incl-last ⊙skel))
  cw-co∂ = GLES.grid-co∂ (ℕ-to-ℤ (S n))

  C-Cofiber-cw-incl-incl-last-iso-Ker-co∂ :
       C (ℕ-to-ℤ (S n)) (⊙Cofiber (⊙cw-incl-tail n≤SSn ⊙skel))
    ≃ᴳ Ker.grp cw-co∂
  C-Cofiber-cw-incl-incl-last-iso-Ker-co∂ =
    Exact2.G-trivial-implies-H-iso-ker
      (exact-seq-index 2 $ GLES.C-cofiber-grid-exact-seq (ℕ-to-ℤ n))
      (exact-seq-index 0 $ GLES.C-cofiber-grid-exact-seq (ℕ-to-ℤ (S n)))
      (C-Cofiber-cw-incl-last-≠-is-trivial (ℕ-to-ℤ (S n)) (ℕ-to-ℤ-≠ (<-to-≠ ltS)) ⊙skel ac)

  module CokerCo∂ =
    Coker (C-is-abelian (ℕ-to-ℤ (S (S n))) (⊙Cofiber (⊙cw-incl-last ⊙skel))) cw-co∂

  -- FIXME favonia: This takes a long time to check. I wonder why?
  Coker-co∂-iso-C-Cofiber-cw-incl-incl-last :
    CokerCo∂.grp ≃ᴳ C (ℕ-to-ℤ (S (S n))) (⊙Cofiber (⊙cw-incl-tail n≤SSn ⊙skel))
  Coker-co∂-iso-C-Cofiber-cw-incl-incl-last =
    Exact2.L-trivial-implies-coker-iso-K
      {G = C (ℕ-to-ℤ (S n)) (⊙Cofiber (⊙cw-incl-last (⊙cw-init ⊙skel)))}
      {H = C (ℕ-to-ℤ (S (S n))) (⊙Cofiber (⊙cw-incl-last ⊙skel))}
      {K = C (ℕ-to-ℤ (S (S n))) (⊙Cofiber (⊙cw-incl-tail n≤SSn ⊙skel))}
      {L = C (ℕ-to-ℤ (S (S n))) (⊙Cofiber (⊙cw-incl-last (⊙cw-init ⊙skel)))}
      (exact-seq-index 1 $ GLES.C-cofiber-grid-exact-seq (ℕ-to-ℤ (S n)))
      (exact-seq-index 2 $ GLES.C-cofiber-grid-exact-seq (ℕ-to-ℤ (S n)))
      (C-is-abelian (ℕ-to-ℤ (S (S n))) (⊙Cofiber (⊙cw-incl-last ⊙skel)))
      (C-Cofiber-cw-incl-last-≠-is-trivial (ℕ-to-ℤ (S (S n))) (≠-inv (ℕ-to-ℤ-≠ (<-to-≠ ltS)))
        (⊙cw-init ⊙skel) (fst ac))
