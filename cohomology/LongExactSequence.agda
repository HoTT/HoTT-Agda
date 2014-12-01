{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.Theory
open import cohomology.CofiberSequence

module cohomology.LongExactSequence {i} (CT : CohomologyTheory i)
  (n : ℤ) {X Y : Ptd i} (f : fst (X ⊙→ Y)) where

open CohomologyTheory CT

long-exact-diag : ExactDiag _ _
long-exact-diag =
  C n (⊙Susp (⊙Cof f))  ⟨ CF-hom n (⊙susp-fmap (⊙cfcod f)) ⟩→
  C n (⊙Susp Y)         ⟨ CF-hom n (⊙susp-fmap f)          ⟩→
  C n (⊙Susp X)         ⟨ CF-hom n ⊙ext-glue               ⟩→
  C n (⊙Cof f)          ⟨ CF-hom n (⊙cfcod f)              ⟩→
  C n Y                 ⟨ CF-hom n f                       ⟩→
  C n X                 ⊣|

long-exact-cofiber : ExactSeq long-exact-diag
long-exact-cofiber = transport
  (λ {(_ , g , h , k) → ExactSeq $
    _ ⟨ CF-hom n k ⟩→ _ ⟨ CF-hom n h ⟩→ _ ⟨ CF-hom n g ⟩→
    _ ⟨ CF-hom n (⊙cfcod f) ⟩→ _ ⟨ CF-hom n f ⟩→ _ ⊣|})
  (cofiber-sequence f)
  (exact-build
    (_ ⟨ CF-hom n (⊙cfcod⁴ f) ⟩→ _ ⟨ CF-hom n (⊙cfcod³ f) ⟩→
     _ ⟨ CF-hom n (⊙cfcod² f) ⟩→ _ ⟨ CF-hom n (⊙cfcod f) ⟩→
     _ ⟨ CF-hom n f ⟩→ _ ⊣|)
    (C-exact n (⊙cfcod³ f)) (C-exact n (⊙cfcod² f))
    (C-exact n (⊙cfcod f)) (C-exact n f))
