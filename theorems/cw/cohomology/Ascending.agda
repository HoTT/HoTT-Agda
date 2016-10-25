{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Theory
open import groups.Exactness
open import groups.HomSequence
open import groups.ExactSequence

open import cw.CW

module cw.cohomology.Ascending {i} (OT : OrdinaryTheory i) where

open OrdinaryTheory OT
open import cw.cohomology.Descending OT
open import cohomology.LongExactSequence cohomology-theory

C-cw-ascending : ∀ {n}
  → (⊙skel : ⊙Skeleton (S (S (S n))))
  → ⊙has-cells-with-choice 0 ⊙skel i
  →  C (ℕ-to-ℤ (S (S n))) (⊙Cofiber (⊙incl-tail (inr (ltSR (ltSR ltS))) ⊙skel))
  ≃ᴳ C (ℕ-to-ℤ (S (S n))) ⊙⟦ ⊙skel ⟧
C-cw-ascending {n} ⊙skel ac =
  Exact2.G-trivial-and-L-trivial-implies-H-iso-K
    (exact-seq-index 1 $ C-cofiber-exact-seq (ℕ-to-ℤ (S n)) (⊙incl-tail n≤SSSn ⊙skel))
    (exact-seq-index 2 $ C-cofiber-exact-seq (ℕ-to-ℤ (S n)) (⊙incl-tail n≤SSSn ⊙skel))
    (C-cw-at-higher (S n) ltS (⊙cw-take n≤SSSn ⊙skel) (fst (fst (fst ac))))
    (C-cw-at-higher (S (S n)) (ltSR ltS) (⊙cw-take n≤SSSn ⊙skel) (fst (fst (fst ac))))
  where
    n≤SSSn : n ≤ S (S (S n))
    n≤SSSn = inr (ltSR (ltSR ltS))
