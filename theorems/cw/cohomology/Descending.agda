{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory
open import groups.Exactness
open import groups.HomSequence
open import groups.ExactSequence

open import cw.CW

module cw.cohomology.Descending {i} (OT : OrdinaryTheory i) where

open OrdinaryTheory OT
open import cw.cohomology.TipAndAugment OT
open import cw.cohomology.WedgeOfCells OT
open import cohomology.LongExactSequence cohomology-theory

private
  C-cw-descend-at-succ : ∀ {n} (⊙skel : ⊙Skeleton (S n))
      {m} (m≠n : m ≠ ℕ-to-ℤ n) (Sm≠n : succ m ≠ ℕ-to-ℤ n)
    → ⊙has-cells-with-choice 0 ⊙skel i
    → C (succ m) ⊙⟦ ⊙skel ⟧ ≃ᴳ C (succ m) ⊙⟦ ⊙cw-init ⊙skel ⟧
  C-cw-descend-at-succ ⊙skel {m} m≠n Sm≠n ac =
    Exact2.G-trivial-and-L-trivial-implies-H-iso-K
      (exact-seq-index 2 $ C-cofiber-exact-seq m (⊙cw-incl-last ⊙skel))
      (exact-seq-index 0 $ C-cofiber-exact-seq (succ m) (⊙cw-incl-last ⊙skel))
      (CXₙ/Xₙ₋₁-≠-is-trivial ⊙skel (succ-≠ m≠n) ac)
      (CXₙ/Xₙ₋₁-≠-is-trivial ⊙skel (succ-≠ Sm≠n) ac)

C-cw-descend : ∀ {n} (⊙skel : ⊙Skeleton (S n))
    {m} (m≠n : m ≠ ℕ-to-ℤ n) (m≠Sn : m ≠ ℕ-to-ℤ (S n))
  → ⊙has-cells-with-choice 0 ⊙skel i
  → C m ⊙⟦ ⊙skel ⟧ ≃ᴳ C m ⊙⟦ ⊙cw-init ⊙skel ⟧
C-cw-descend ⊙skel {m = negsucc m} -Sm≠n -Sm≠Sn
  = C-cw-descend-at-succ ⊙skel (pred-≠ -Sm≠Sn) -Sm≠n
C-cw-descend ⊙skel {m = pos O} O≠n O≠Sn
  = C-cw-descend-at-succ ⊙skel (pred-≠ O≠Sn) O≠n
C-cw-descend ⊙skel {m = pos (S n)} Sm≠n Sm≠Sn
  = C-cw-descend-at-succ ⊙skel (pred-≠ Sm≠Sn) Sm≠n

abstract
  C-cw-at-higher : ∀ {n} (⊙skel : ⊙Skeleton n) {m} (n<m : n < m)
    → ⊙has-cells-with-choice 0 ⊙skel i
    → is-trivialᴳ (C (ℕ-to-ℤ m) ⊙⟦ ⊙skel ⟧)
  C-cw-at-higher {n = O} ⊙skel 0<n ac =
    CX₀-≠-is-trivial ⊙skel (ℕ-to-ℤ-≠ (≠-inv (<-to-≠ 0<n))) ac
  C-cw-at-higher {n = S n} ⊙skel Sn<m ac =
    iso-preserves'-trivial
      (C-cw-descend ⊙skel
        (ℕ-to-ℤ-≠ (≠-inv (<-to-≠ (<-trans ltS Sn<m))))
        (ℕ-to-ℤ-≠ (≠-inv (<-to-≠ Sn<m)))
        ac)
      (C-cw-at-higher (⊙cw-init ⊙skel) (<-trans ltS Sn<m) (⊙init-has-cells-with-choice ⊙skel ac))

  C-cw-at-negsucc : ∀ {n} (⊙skel : ⊙Skeleton n) m
    → ⊙has-cells-with-choice 0 ⊙skel i
    → is-trivialᴳ (C (negsucc m) ⊙⟦ ⊙skel ⟧)
  C-cw-at-negsucc {n = O} ⊙skel m ac =
    CX₀-≠-is-trivial ⊙skel (ℤ-negsucc≠pos m O) ac
  C-cw-at-negsucc {n = S n} ⊙skel m ac =
    iso-preserves'-trivial
      (C-cw-descend ⊙skel
        (ℤ-negsucc≠pos _ n)
        (ℤ-negsucc≠pos _ (S n))
        ac)
      (C-cw-at-negsucc (⊙cw-init ⊙skel) m (⊙init-has-cells-with-choice ⊙skel ac))

C-cw-descend-at-lower : ∀ {n} (⊙skel : ⊙Skeleton (S n)) {m} (m<n : m < n)
  → ⊙has-cells-with-choice 0 ⊙skel i
  → C (ℕ-to-ℤ m) ⊙⟦ ⊙skel ⟧ ≃ᴳ C (ℕ-to-ℤ m) ⊙⟦ ⊙cw-init ⊙skel ⟧
C-cw-descend-at-lower ⊙skel m<n ac =
  C-cw-descend ⊙skel (ℕ-to-ℤ-≠ (<-to-≠ m<n)) (ℕ-to-ℤ-≠ (<-to-≠ (ltSR m<n))) ac

{-
favonia: it turns out easier (?) to do the descending step by step

C-cw-to-diag-at-lower : ∀ n {m} (Sn≤m : S n ≤ m) (⊙skel : ⊙Skeleton m)
  → ⊙has-cells-with-choice 0 ⊙skel i
  → C (ℕ-to-ℤ n) ⊙⟦ ⊙skel ⟧ ≃ᴳ C (ℕ-to-ℤ n) ⊙⟦ ⊙cw-take Sn≤m ⊙skel ⟧
C-cw-to-diag-at-lower _ (inl idp) _ _ = idiso _
C-cw-to-diag-at-lower n (inr ltS) ⊙skel ac =
  C-cw-descend (ℕ-to-ℤ n) (ℕ-to-ℤ-≠ (<-to-≠ ltS)) (ℕ-to-ℤ-≠ (<-to-≠ (ltSR ltS))) ⊙skel ac
C-cw-to-diag-at-lower n {S m} (inr (ltSR lt)) ⊙skel ac =
      C-cw-to-diag-at-lower n (inr lt) (⊙cw-init ⊙skel) (⊙init-has-cells-with-choice ⊙skel ac)
  ∘eᴳ C-cw-descend (ℕ-to-ℤ n) (ℕ-to-ℤ-≠ n≠m) (ℕ-to-ℤ-≠ n≠Sm) ⊙skel ac
  where
    n≠Sm : n ≠ S m
    n≠Sm = <-to-≠ (<-trans ltS (ltSR lt))

    n≠m : n ≠ m
    n≠m = <-to-≠ (<-trans ltS lt)
-}
