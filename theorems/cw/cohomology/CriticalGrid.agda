{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Theory
open import groups.Exactness
open import groups.HomSequence
open import groups.ExactSequence

open import cw.CW

module cw.cohomology.CriticalGrid {i} (OT : OrdinaryTheory i) where

open OrdinaryTheory OT
open import cw.cohomology.Descending OT
open import cohomology.LongExactSequence cohomology-theory

module _ {n} (⊙skel : ⊙Skeleton {i} (S (S (S n))))
  (ac : ⊙has-cells-with-choice 0 ⊙skel i) where

  private
    n≤SSSn : n ≤ S (S (S n))
    n≤SSSn = inr (ltSR (ltSR ltS))

    ⊙skel₋₃ = ⊙cw-take n≤SSSn ⊙skel
    ac₋₃ = fst (fst (fst ac))

  C-cw-ascending :
       C (ℕ-to-ℤ (S (S n))) (⊙Cofiber (⊙cw-incl-tail n≤SSSn ⊙skel))
    ≃ᴳ C (ℕ-to-ℤ (S (S n))) ⊙⟦ ⊙skel ⟧
  C-cw-ascending = Exact2.G-trivial-and-L-trivial-implies-H-iso-K
    (exact-seq-index 1 $ C-cofiber-exact-seq (ℕ-to-ℤ (S n)) (⊙cw-incl-tail n≤SSSn ⊙skel))
    (exact-seq-index 2 $ C-cofiber-exact-seq (ℕ-to-ℤ (S n)) (⊙cw-incl-tail n≤SSSn ⊙skel))
    (C-cw-at-higher (S n) ltS ⊙skel₋₃ ac₋₃)
    (C-cw-at-higher (S (S n)) (ltSR ltS) ⊙skel₋₃ ac₋₃)
