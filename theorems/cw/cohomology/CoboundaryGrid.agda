{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory
open import groups.Exactness
open import groups.HomSequence
open import groups.ExactSequence

open import cw.CW

module cw.cohomology.CoboundaryGrid {i} (OT : OrdinaryTheory i)
  {n} (⊙skel : ⊙Skeleton {i} (S (S n))) (ac : ⊙has-cells-with-choice 0 ⊙skel i) where

open OrdinaryTheory OT
open import cw.cohomology.Descending OT
open import cw.cohomology.WedgeOfCells OT
open import cw.cohomology.GridPtdMap (⊙cw-incl-last (⊙cw-init ⊙skel)) (⊙cw-incl-last ⊙skel)
import cw.cohomology.GridLongExactSequence
private
  module GLES n = cw.cohomology.GridLongExactSequence
    cohomology-theory n (⊙cw-incl-last (⊙cw-init ⊙skel)) (⊙cw-incl-last ⊙skel)

{-
  Xn --> X(n+1) -----> X(n+2)
   |       |             |
   v       v             v
   1 -> X(n+1)/n -> X(n+2)/(n+1)
           |    this     |
           v      one    v
           1 -------> X(n+2)/n
-}

private
  n≤SSn : n ≤ S (S n)
  n≤SSn = inr (ltSR ltS)

cw-co∂-last : C (ℕ-to-ℤ (S n)) (⊙Cofiber (⊙cw-incl-last (⊙cw-init ⊙skel)))
           →ᴳ C (ℕ-to-ℤ (S (S n))) (⊙Cofiber (⊙cw-incl-last ⊙skel))
cw-co∂-last = GLES.grid-co∂ (ℕ-to-ℤ (S n))

Ker-cw-co∂-last : C (ℕ-to-ℤ (S n)) (⊙Cofiber (⊙cw-incl-tail n≤SSn ⊙skel))
               ≃ᴳ Ker.grp cw-co∂-last
Ker-cw-co∂-last = Exact2.G-trivial-implies-H-iso-ker
  (exact-seq-index 2 $ GLES.C-grid-cofiber-exact-seq (ℕ-to-ℤ n))
  (exact-seq-index 0 $ GLES.C-grid-cofiber-exact-seq (ℕ-to-ℤ (S n)))
  (C-Cofiber-cw-incl-last-<-is-trivial (S n) ltS ⊙skel ac)

private
  -- separate lemmas to speed up the type checking
  abstract
    lemma₁-abelian : is-abelian (C (ℕ-to-ℤ (S (S n))) (⊙Cofiber (⊙cw-incl-last ⊙skel)))
    lemma₁-abelian = C-is-abelian (ℕ-to-ℤ (S (S n))) (⊙Cofiber (⊙cw-incl-last ⊙skel))

module CokerCo∂ = Coker cw-co∂-last lemma₁-abelian

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
    lemma₁-trivial = C-Cofiber-cw-incl-last->-is-trivial (S (S n)) ltS (⊙cw-init ⊙skel) (fst ac)

-- FIXME favonia: This still takes a long time to check. I wonder why?
Coker-cw-co∂-last : CokerCo∂.grp ≃ᴳ C (ℕ-to-ℤ (S (S n))) (⊙Cofiber (⊙cw-incl-tail n≤SSn ⊙skel))
Coker-cw-co∂-last = Exact2.L-trivial-implies-coker-iso-K
  lemma₁-exact₀ lemma₁-exact₁ lemma₁-abelian lemma₁-trivial
