{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.OrdinaryTheory
open import cohomology.CofiberSequence

module cohomology.LongExactSequence {i} (OT : OrdinaryTheory i)
  (n : ℕ) {X Y : Ptd i} (f : fst (X ∙→ Y)) where

open OrdinaryTheory OT

co∂-exact-left-itok : is-exact-itok-mere (CF n (ptd-co∂ f)) (CF n (ptd-cfcod f))
co∂-exact-left-itok = transport
  (λ {(_ , h) → is-exact-itok-mere (CF n h) (CF n (ptd-cfcod f))})
  (co∂-is-cfcod² f)
  (C-exact-itok-mere n (ptd-cfcod f))

co∂-exact-left-ktoi : is-exact-ktoi-mere (CF n (ptd-co∂ f)) (CF n (ptd-cfcod f))
co∂-exact-left-ktoi = transport
  (λ {(_ , h) → is-exact-ktoi-mere (CF n h) (CF n (ptd-cfcod f))})
  (co∂-is-cfcod² f)
  (C-exact-ktoi-mere n (ptd-cfcod f))

co∂-exact-right-itok :
  is-exact-itok-mere (CF n (ptd-susp-fmap f)) (CF n (ptd-co∂ f))
co∂-exact-right-itok = transport
  (λ {(_ , (g , h)) → is-exact-itok-mere (CF n h) (CF n g)})
  (cofiber-sequence f)
  (C-exact-itok-mere n (ptd-cfcod (ptd-cfcod f)))

co∂-exact-right-ktoi :
  is-exact-ktoi-mere (CF n (ptd-susp-fmap f)) (CF n (ptd-co∂ f))
co∂-exact-right-ktoi = transport
  (λ {(_ , (g , h)) → is-exact-ktoi-mere (CF n h) (CF n g)})
  (cofiber-sequence f)
  (C-exact-ktoi-mere n (ptd-cfcod (ptd-cfcod f)))
