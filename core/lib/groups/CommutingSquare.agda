{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Group
open import lib.types.CommutingSquare
open import lib.groups.Homomorphism
open import lib.groups.Isomorphism

module lib.groups.CommutingSquare where

-- A new type to keep the parameters.
record CommSquareᴳ {i₀ i₁ j₀ j₁}
  {G₀ : Group i₀} {G₁ : Group i₁} {H₀ : Group j₀} {H₁ : Group j₁}
  (φ₀ : G₀ →ᴳ H₀) (φ₁ : G₁ →ᴳ H₁) (ξG : G₀ →ᴳ G₁) (ξH : H₀ →ᴳ H₁)
  : Type (lmax (lmax i₀ i₁) (lmax j₀ j₁)) where
  constructor comm-sqrᴳ
  field
    commutesᴳ : ∀ g₀ → GroupHom.f (ξH ∘ᴳ φ₀) g₀ == GroupHom.f (φ₁ ∘ᴳ ξG) g₀

infix 0 _□$ᴳ_
_□$ᴳ_ = CommSquareᴳ.commutesᴳ

CommSquareᴳ-inverse-v : ∀ {i₀ i₁ j₀ j₁}
  {G₀ : Group i₀} {G₁ : Group i₁} {H₀ : Group j₀} {H₁ : Group j₁}
  {φ₀ : G₀ →ᴳ H₀} {φ₁ : G₁ →ᴳ H₁} {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁}
  → CommSquareᴳ φ₀ φ₁ ξG ξH
  → (ξG-ise : is-equiv (GroupHom.f ξG)) (ξH-ise : is-equiv (GroupHom.f ξH))
  → CommSquareᴳ φ₁ φ₀ (GroupIso.g-hom (ξG , ξG-ise)) (GroupIso.g-hom (ξH , ξH-ise))
CommSquareᴳ-inverse-v (comm-sqrᴳ □) ξG-ise ξH-ise =
  comm-sqrᴳ (commutes (CommSquare-inverse-v (comm-sqr □) ξG-ise ξH-ise))

