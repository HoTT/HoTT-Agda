{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.OrdinaryTheory
open import cohomology.CofiberSequence

module cohomology.LongExactSequence {i} (OT : OrdinaryTheory i)
  (n : ℕ) {X Y : Ptd i} (f : fst (X ∙→ Y)) where

open OrdinaryTheory OT

co∂-exact-left : is-exact (CF n (ptd-co∂ f)) (CF n (ptd-cfcod f))
co∂-exact-left = transport
  (λ {(_ , h) → is-exact (CF n h) (CF n (ptd-cfcod f))})
  (co∂-is-cfcod² f)
  (C-exact n (ptd-cfcod f))

co∂-exact-right : is-exact (CF n (ptd-susp-fmap f)) (CF n (ptd-co∂ f))
co∂-exact-right = transport
  (λ {(_ , (g , h)) → is-exact (CF n h) (CF n g)})
  (cofiber-sequence f)
  (C-exact n (ptd-cfcod (ptd-cfcod f)))

long-exact-diag : ExactDiag _ _
long-exact-diag =
  C n (Ptd-Susp Y) ⟨ CF-hom n (ptd-susp-fmap f) ⟩→
  C n (Ptd-Susp X) ⟨ CF-hom n (ptd-co∂ f)       ⟩→
  C n (Ptd-Cof f)  ⟨ CF-hom n (ptd-cfcod f)     ⟩→
  C n Y            ⟨ CF-hom n f                 ⟩→
  C n X            ⊣|

long-exact-cofiber : ExactSeq long-exact-diag
long-exact-cofiber = exact-build long-exact-diag
  co∂-exact-right co∂-exact-left (C-exact n f)
