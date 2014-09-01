{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.OrdinaryTheory
open import cohomology.CofiberSequence

module cohomology.LongExactSequence {i} (OT : OrdinaryTheory i)
  (n : ℤ) {X Y : Ptd i} (f : fst (X ∙→ Y)) where

open OrdinaryTheory OT

long-exact-diag : ExactDiag _ _
long-exact-diag =
  C n (Ptd-Susp (Ptd-Cof f))  ⟨ CF-hom n (ptd-susp-fmap (ptd-cfcod f)) ⟩→
  C n (Ptd-Susp Y)            ⟨ CF-hom n (ptd-susp-fmap f)             ⟩→
  C n (Ptd-Susp X)            ⟨ CF-hom n ptd-ext-glue                  ⟩→
  C n (Ptd-Cof f)             ⟨ CF-hom n (ptd-cfcod f)                 ⟩→
  C n Y                       ⟨ CF-hom n f                             ⟩→
  C n X                       ⊣|

long-exact-cofiber : ExactSeq long-exact-diag
long-exact-cofiber = transport
  (λ {(_ , g , h , k) → ExactSeq $
    _ ⟨ CF-hom n k ⟩→ _ ⟨ CF-hom n h ⟩→ _ ⟨ CF-hom n g ⟩→
    _ ⟨ CF-hom n (ptd-cfcod f) ⟩→ _ ⟨ CF-hom n f ⟩→ _ ⊣|})
  (cofiber-sequence f)
  (exact-build
    (_ ⟨ CF-hom n (ptd-cfcod⁴ f) ⟩→ _ ⟨ CF-hom n (ptd-cfcod³ f) ⟩→
     _ ⟨ CF-hom n (ptd-cfcod² f) ⟩→ _ ⟨ CF-hom n (ptd-cfcod f) ⟩→
     _ ⟨ CF-hom n f ⟩→ _ ⊣|)
    (C-exact n (ptd-cfcod³ f)) (C-exact n (ptd-cfcod² f))
    (C-exact n (ptd-cfcod f)) (C-exact n f))
