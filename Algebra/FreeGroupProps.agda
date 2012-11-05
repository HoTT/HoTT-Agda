{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.TruncatedHIT
open import Integers

module Algebra.FreeGroupProps {i} (A : Set i) ⦃ p : is-set A ⦄ where

import Algebra.FreeGroup
open Algebra.FreeGroup A

abstract
  freegroup-is-set : is-set freegroup
  freegroup-is-set =
    spheres-filled-is-hlevel 2 freegroup (λ ()) (λ f → (top f , rays f))

x·-is-equiv : (x : A) → is-equiv (λ u → x · u)
x·-is-equiv x = iso-is-eq (λ u → x · u)
  (λ u → x ⁻¹· u)
  (right-inverse-· x)
  (left-inverse-· x)
