{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Theory
open import groups.Exactness
open import groups.HomSequence

open import cw.CW

module cw.cohomology.Descending {i} (OT : OrdinaryTheory i) where

open OrdinaryTheory OT
open import cw.cohomology.WedgeOfCells OT
open import cohomology.LongExactSequence cohomology-theory

private
  C-cw-descend-at-succ : ∀ n {m} (n≠m : n ≠ ℕ-to-ℤ m) (Sn≠m : succ n ≠ ℕ-to-ℤ m)
    → (⊙skel : ⊙Skeleton (S m))
    → ⊙has-cells-with-choice 0 ⊙skel i
    → C (succ n) ⊙⟦ ⊙skel ⟧ ≃ᴳ C (succ n) ⊙⟦ ⊙cw-init ⊙skel ⟧
  C-cw-descend-at-succ n {m} n≠m Sn≠m ⊙skel ac =
    Exact2.G-trivial-and-L-trivial-implies-H-iso-K
      (fst $ snd $ snd $ C-cofiber-seq-is-exact n (⊙incl-last ⊙skel))
      (fst $ C-cofiber-seq-is-exact (succ n) (⊙incl-last ⊙skel))
      (C-incl-last-≠-is-trivial (succ n) (succ-≠ n≠m) ⊙skel ac)
      (C-incl-last-≠-is-trivial (succ (succ n)) (succ-≠ Sn≠m) ⊙skel ac)

C-cw-descend : ∀ n {m} (n≠Sm : n ≠ ℕ-to-ℤ (S m)) (n≠m : n ≠ ℕ-to-ℤ m)
  → (⊙skel : ⊙Skeleton (S m))
  → ⊙has-cells-with-choice 0 ⊙skel i
  → C n ⊙⟦ ⊙skel ⟧ ≃ᴳ C n ⊙⟦ ⊙cw-init ⊙skel ⟧
C-cw-descend (negsucc n) -Sn≠Sm -Sn≠m
  = C-cw-descend-at-succ (negsucc (S n)) (pred-≠ -Sn≠Sm) -Sn≠m
C-cw-descend (pos O) -O≠Sm -O≠m
  = C-cw-descend-at-succ -1 (pred-≠ -O≠Sm) -O≠m
C-cw-descend (pos (S n)) Sn≠Sm Sn≠m
  = C-cw-descend-at-succ (pos n) (pred-≠ Sn≠Sm) Sn≠m

C-cw-at-higher : ∀ n {m} (m<n : m < n) (⊙skel : ⊙Skeleton m)
  → ⊙has-cells-with-choice 0 ⊙skel i
  → is-trivialᴳ (C (ℕ-to-ℤ n) ⊙⟦ ⊙skel ⟧)
C-cw-at-higher n {m = O} 0<n ⊙skel ac =
  C-points-≠-is-trivial (ℕ-to-ℤ-≠ (≠-inv (<-to-≠ 0<n))) ⊙skel ac
C-cw-at-higher n {m = S m} Sm<n ⊙skel ac =
  iso-preserves'-trivial
    (C-cw-descend (ℕ-to-ℤ n)
      (ℕ-to-ℤ-≠ (≠-inv (<-to-≠ Sm<n)))
      (ℕ-to-ℤ-≠ (≠-inv (<-to-≠ (<-trans ltS Sm<n))))
      ⊙skel ac)
    (C-cw-at-higher n (<-trans ltS Sm<n) (⊙cw-init ⊙skel) (fst ac))

C-cw-at-negsucc : ∀ n {m} (⊙skel : ⊙Skeleton m)
  → ⊙has-cells-with-choice 0 ⊙skel i
  → is-trivialᴳ (C (negsucc n) ⊙⟦ ⊙skel ⟧)
C-cw-at-negsucc n {m = O} ⊙skel ac =
  C-points-≠-is-trivial (ℤ-negsucc≠pos n O) ⊙skel ac
C-cw-at-negsucc n {m = S m} ⊙skel ac =
  iso-preserves'-trivial
    (C-cw-descend (negsucc n)
      (ℤ-negsucc≠pos _ (S m))
      (ℤ-negsucc≠pos _ m)
      ⊙skel ac)
    (C-cw-at-negsucc n (⊙cw-init ⊙skel) (fst ac))

C-cw-to-diag-at-lower : ∀ n {m} (Sn≤m : S n ≤ m) (⊙skel : ⊙Skeleton m)
  → ⊙has-cells-with-choice 0 ⊙skel i
  → C (ℕ-to-ℤ n) ⊙⟦ ⊙skel ⟧ ≃ᴳ C (ℕ-to-ℤ n) ⊙⟦ ⊙cw-take Sn≤m ⊙skel ⟧
C-cw-to-diag-at-lower _ (inl idp) _ _ = idiso _
C-cw-to-diag-at-lower n (inr ltS) ⊙skel ac =
  C-cw-descend (ℕ-to-ℤ n) (ℕ-to-ℤ-≠ (<-to-≠ (ltSR ltS))) (ℕ-to-ℤ-≠ (<-to-≠ ltS)) ⊙skel ac
C-cw-to-diag-at-lower n (inr (ltSR lt)) ⊙skel ac =
      C-cw-to-diag-at-lower n (inr lt) (⊙cw-init ⊙skel) (fst ac)
  ∘eᴳ C-cw-descend (ℕ-to-ℤ n) (ℕ-to-ℤ-≠ (<-to-≠ (<-trans ltS (ltSR lt)))) (ℕ-to-ℤ-≠ (<-to-≠ (<-trans ltS lt))) ⊙skel ac
