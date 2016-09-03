{-# OPTIONS --without-K #-}

open import HoTT

-- This file is temporarily put in the cw/ directory for
-- development, but it actually belongs to somewhere else.

module cw.SphereEndomorphism where

  ⊙Sphere-endo-out :
    ∀ n → Trunc 0 (fst (⊙Sphere (S n) ⊙→ ⊙Sphere (S n))) → Trunc 0 (Sphere (S n) → Sphere (S n))
  ⊙Sphere-endo-out n = Trunc-rec Trunc-level ([_] ∘ fst)

  -- TODO
  -- for [Sphere 0], by commutativity
  -- for [Sphere (S n)], by connectivity
  postulate
    ⊙Sphere-endo-out-is-equiv : ∀ n → is-equiv (⊙Sphere-endo-out n)

  ⊙Sphere-endo-in = λ n → is-equiv.g (⊙Sphere-endo-out-is-equiv n)
