{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory
open import groups.Exactness
open import groups.ExactSequence

open import cw.CW

module cw.cohomology.HigherCoboundaryGrid {i} (OT : OrdinaryTheory i)
  {n} (⊙skel : ⊙Skeleton {i} (S (S n))) (ac : ⊙has-cells-with-choice 0 ⊙skel i) where

open OrdinaryTheory OT
open import cw.cohomology.WedgeOfCells OT
open import cw.cohomology.HigherCoboundary OT ⊙skel
open import cw.cohomology.GridPtdMap (⊙cw-incl-last (⊙cw-init ⊙skel)) (⊙cw-incl-last ⊙skel)
import cw.cohomology.GridLongExactSequence
private
  module GLES n = cw.cohomology.GridLongExactSequence
    cohomology-theory n (⊙cw-incl-last (⊙cw-init ⊙skel)) (⊙cw-incl-last ⊙skel)

{-
  Xn --> X(n+1) -----> X(n+2)
   |       |             |
   v       v             v
   1 -> X(n+1)/n ---> X(n+2)/n
           |    this     |
           v      one    v
           1 -----> X(n+2)/(n+1)
-}

private
  n≤SSn : n ≤ S (S n)
  n≤SSn = inr (ltSR ltS)

private
  -- separate lemmas to speed up the type checking
  abstract
    lemma₀-exact₀ : is-exact
      (C-fmap (ℕ-to-ℤ (S n)) Z/X-to-Z/Y)
      (C-fmap (ℕ-to-ℤ (S n)) Y/X-to-Z/X)
    lemma₀-exact₀ = exact-seq-index 2 $ GLES.C-grid-cofiber-exact-seq (ℕ-to-ℤ n)

    lemma₀-exact₁ : is-exact (C-fmap (ℕ-to-ℤ (S n)) Y/X-to-Z/X) cw-co∂-last
    lemma₀-exact₁ = exact-seq-index 0 $ GLES.C-grid-cofiber-exact-seq (ℕ-to-ℤ (S n))

    lemma₀-trivial : is-trivialᴳ (C (ℕ-to-ℤ (S n)) Z/Y)
    lemma₀-trivial = CXₙ/Xₙ₋₁-<-is-trivial ⊙skel ltS ac

Ker-cw-co∂-last : C (ℕ-to-ℤ (S n)) (⊙Cofiber (⊙cw-incl-tail n≤SSn ⊙skel))
               ≃ᴳ Ker.grp cw-co∂-last
Ker-cw-co∂-last = Exact2.G-trivial-implies-H-iso-ker
  lemma₀-exact₀ lemma₀-exact₁ lemma₀-trivial

private
  -- separate lemmas to speed up the type checking
  abstract
    lemma₁-exact₀ : is-exact cw-co∂-last (C-fmap (ℕ-to-ℤ (S (S n))) Z/X-to-Z/Y)
    lemma₁-exact₀ = exact-seq-index 1 $ GLES.C-grid-cofiber-exact-seq (ℕ-to-ℤ (S n))

    lemma₁-exact₁ : is-exact
      (C-fmap (ℕ-to-ℤ (S (S n))) Z/X-to-Z/Y)
      (C-fmap (ℕ-to-ℤ (S (S n))) Y/X-to-Z/X)
    lemma₁-exact₁ = exact-seq-index 2 $ GLES.C-grid-cofiber-exact-seq (ℕ-to-ℤ (S n))

    lemma₁-trivial : is-trivialᴳ (C (ℕ-to-ℤ (S (S n))) Y/X)
    lemma₁-trivial = CXₙ/Xₙ₋₁->-is-trivial (⊙cw-init ⊙skel) ltS
      (⊙init-has-cells-with-choice ⊙skel ac)

Coker-cw-co∂-last : CokerCo∂ ≃ᴳ C (ℕ-to-ℤ (S (S n))) (⊙Cofiber (⊙cw-incl-tail n≤SSn ⊙skel))
Coker-cw-co∂-last = Exact2.L-trivial-implies-coker-iso-K
  lemma₁-exact₀ lemma₁-exact₁ (CXₙ/Xₙ₋₁-is-abelian ⊙skel (ℕ-to-ℤ (S (S n)))) lemma₁-trivial
