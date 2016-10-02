{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.CircleHSpace
open import homotopy.JoinAssocCubical
open import homotopy.JoinSusp

module homotopy.Hopf where

import homotopy.HopfConstruction
module Hopf = homotopy.HopfConstruction S¹-conn ⊙S¹-hSpace

Hopf : S² → Type₀
Hopf = Hopf.H.f

Hopf-fiber : Hopf north == S¹
Hopf-fiber = idp

-- TODO Turn [Hopf.theorem] into an equivalence
Hopf-total : Σ _ Hopf ≃ S³
Hopf-total =
  Σ _ Hopf       ≃⟨ coe-equiv Hopf.theorem ⟩
  S¹ * S¹        ≃⟨ *-Susp-l S⁰ S¹ ⟩
  Susp (S⁰ * S¹) ≃⟨ Susp-emap (*-Bool-l S¹) ⟩
  S³ ≃∎
