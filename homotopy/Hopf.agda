{-# OPTIONS --without-K #-}

open import HoTT
import homotopy.HopfConstruction
open import homotopy.CircleHSpace
open import homotopy.SuspensionJoin using () renaming (e to suspension-join)
open import homotopy.S1SuspensionS0 using () renaming (e to S¹≃SuspensionS⁰)
import homotopy.JoinAssoc

module homotopy.Hopf where

-- To move
S⁰ = Bool
S² = Suspension S¹
S³ = Suspension S²

-- To move
S¹-connected : is-connected ⟨0⟩ S¹
S¹-connected =
  ([ base ] , Trunc-elim (λ x → =-preserves-level ⟨0⟩ Trunc-level)
             (S¹-elim idp (prop-has-all-paths-↓ ((Trunc-level :> is-set (Trunc ⟨0⟩ S¹)) _ _))))

module Hopf = homotopy.HopfConstruction S¹ S¹-connected S¹-hSpace

Hopf : S² → Type₀
Hopf = Hopf.H.f

Hopf-fiber : Hopf (north _) == S¹
Hopf-fiber = idp

Hopf-total : Σ _ Hopf == S³
Hopf-total =
  Σ _ Hopf               =⟨ Hopf.theorem ⟩
  S¹ * S¹                =⟨ ua S¹≃SuspensionS⁰ |in-ctx (λ u → u * S¹) ⟩
  (Suspension S⁰) * S¹   =⟨ ua (suspension-join S⁰) |in-ctx (λ u → u * S¹) ⟩
  (S⁰ * S⁰) * S¹         =⟨ ua (homotopy.JoinAssoc.*-assoc S⁰ S⁰ S¹) ⟩
  S⁰ * (S⁰ * S¹)         =⟨ ! (ua (suspension-join S¹)) |in-ctx (λ u → S⁰ * u) ⟩
  S⁰ * S²                =⟨ ! (ua (suspension-join S²)) ⟩
  S³ ∎
