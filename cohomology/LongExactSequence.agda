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
