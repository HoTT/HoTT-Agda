{-# OPTIONS --without-K #-}

open import HoTT

module groups.HomMap where

{- maps between two homs -}

record HomCommSquare {i₀ i₁ j₀ j₁}
  {G₀ : Group i₀} {G₁ : Group i₁} {H₀ : Group j₀} {H₁ : Group j₁}
  (φ₀ : G₀ →ᴳ H₀) (φ₁ : G₁ →ᴳ H₁) (ξG : G₀ →ᴳ G₁) (ξH : H₀ →ᴳ H₁)
  : Type (lmax (lmax i₀ i₁) (lmax j₀ j₁)) where

  field
    commutes : ∀ g₀ → GroupHom.f (ξH ∘ᴳ φ₀) g₀ == GroupHom.f (φ₁ ∘ᴳ ξG) g₀

commutesᴳ = HomCommSquare.commutes

abstract
  HomComm-∘h : ∀ {i₀ i₁ i₂ j₀ j₁ j₂}
    {G₀ : Group i₀} {G₁ : Group i₁} {G₂ : Group i₂}
    {H₀ : Group j₀} {H₁ : Group j₁} {H₂ : Group j₂}
    {φ₀ : G₀ →ᴳ H₀} {φ₁ : G₁ →ᴳ H₁} {φ₂ : G₂ →ᴳ H₂}
    {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁}
    {ζG : G₁ →ᴳ G₂} {ζH : H₁ →ᴳ H₂}
    → HomCommSquare φ₀ φ₁ ξG ξH
    → HomCommSquare φ₁ φ₂ ζG ζH
    → HomCommSquare φ₀ φ₂ (ζG ∘ᴳ ξG) (ζH ∘ᴳ ξH)
  HomComm-∘h {ξG = ξG} {ζH = ζH} s₀₁ s₁₂ = record {
    commutes = λ g₀ → ap (GroupHom.f ζH) (commutesᴳ s₀₁ g₀)
                    ∙ commutesᴳ s₁₂ (GroupHom.f ξG g₀)}
