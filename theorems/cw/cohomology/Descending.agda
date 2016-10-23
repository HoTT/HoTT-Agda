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

C-descend₁ : ∀ n {m} (n≠m : n ≠ ℕ-to-ℤ m) (Sn≠m : succ n ≠ ℕ-to-ℤ m)
  → (⊙skel : ⊙Skeleton (S m))
  → ⊙has-cells-with-choice 0 ⊙skel i
  → C (succ n) ⊙⟦ ⊙skel ⟧ ≃ᴳ C (succ n) ⊙⟦ ⊙cw-init ⊙skel ⟧
C-descend₁ n {m} n≠m Sn≠m ⊙skel ac =
  Exact2.G-trivial-and-L-trivial-implies-H-iso-K
    (fst $ snd $ snd $ C-cofiber-seq-is-exact n (⊙incl-last ⊙skel))
    (fst $ C-cofiber-seq-is-exact (succ n) (⊙incl-last ⊙skel))
    (C-incl-last-≠-is-trivial (succ n) (succ-≠ n≠m) ⊙skel ac)
    (C-incl-last-≠-is-trivial (succ (succ n)) (succ-≠ Sn≠m) ⊙skel ac)

C-descend-at-higher : ∀ n {m} (m<n : m < n) (⊙skel : ⊙Skeleton m)
  → ⊙has-cells-with-choice 0 ⊙skel i
  → is-trivialᴳ (C (ℕ-to-ℤ n) ⊙⟦ ⊙skel ⟧)
C-descend-at-higher n {m = O} 0<n ⊙skel ac =
  C-points-≠-is-trivial (ℕ-to-ℤ-≠ (≠-inv (<-to-≠ 0<n))) ⊙skel ac
C-descend-at-higher O m<O _ _ = ⊥-rec (≮O _ m<O)
C-descend-at-higher (S n) {m = S m} Sm<Sn ⊙skel ac =
  iso-preserves'-trivial
    (C-descend₁ (ℕ-to-ℤ n)
      (ℕ-to-ℤ-≠ (≠-inv (<-to-≠ (<-cancel-S Sm<Sn))))
      (ℕ-to-ℤ-≠ (≠-inv (<-to-≠ (<-trans ltS Sm<Sn))))
      ⊙skel ac)
    (C-descend-at-higher (S n) (<-trans ltS Sm<Sn) (⊙cw-init ⊙skel) (fst ac))
