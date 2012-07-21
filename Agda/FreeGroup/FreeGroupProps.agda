{-# OPTIONS --without-K #-}

open import Base
open import Truncation.SphereFillings

module FreeGroup.FreeGroupProps {i : Level} (A : Set i) ⦃ p : is-set A ⦄ where

import FreeGroup.FreeGroup
open FreeGroup.FreeGroup A

abstract
  freegroup-is-set : is-set freegroup
  freegroup-is-set = n-spheres-filled-hlevel 2 freegroup (λ f → (top f , rays f))

x·-is-equiv : (x : A) → is-equiv (λ u → x · u)
x·-is-equiv x = iso-is-eq (λ u → x · u) (λ u → x ⁻¹· u) (right-inverse-· x) (left-inverse-· x)

-- f-path : A → freegroup ≡ freegroup
-- f-path x = eq-to-path (_ , f-equiv x)
