{-# OPTIONS --without-K #-}

open import HoTT
import homotopy.HopfConstruction
open import homotopy.CircleHSpace
open import homotopy.SuspensionJoin using () renaming (e to suspension-join)
import homotopy.JoinAssocCubical

module homotopy.Hopf where

module Hopf = homotopy.HopfConstruction S¹-conn ⊙S¹-hSpace

Hopf : S² → Type₀
Hopf = Hopf.H.f

Hopf-fiber : Hopf north == S¹
Hopf-fiber = idp

-- TODO Turn this into an equivalence
Hopf-total : Σ _ Hopf == S³
Hopf-total =
  Σ _ Hopf       =⟨ Hopf.theorem ⟩
  S¹ * S¹        =⟨ ua (suspension-join S⁰) |in-ctx (λ u → u * S¹) ⟩
  (S⁰ * S⁰) * S¹ =⟨ ua homotopy.JoinAssocCubical.*-assoc ⟩
  S⁰ * (S⁰ * S¹) =⟨ ! (ua (suspension-join S¹)) |in-ctx (λ u → S⁰ * u) ⟩
  S⁰ * S²        =⟨ ! (ua (suspension-join S²)) ⟩
  S³ ∎
