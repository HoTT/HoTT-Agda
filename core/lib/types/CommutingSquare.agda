{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Sigma

module lib.types.CommutingSquare where

{- maps between two functions -}

record CommSquare {i₀ i₁ j₀ j₁}
  {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
  (f₀ : A₀ → B₀) (f₁ : A₁ → B₁) (hA : A₀ → A₁) (hB : B₀ → B₁)
  : Type (lmax (lmax i₀ i₁) (lmax j₀ j₁)) where
  constructor comm-sqr
  field
    commutes : ∀ a₀ → (hB ∘ f₀) a₀ == (f₁ ∘ hA) a₀

open CommSquare public

CommSquare-∘h : ∀ {i₀ i₁ i₂ j₀ j₁ j₂}
  {A₀ : Type i₀} {A₁ : Type i₁} {A₂ : Type i₂}
  {B₀ : Type j₀} {B₁ : Type j₁} {B₂ : Type j₂}
  {f₀ : A₀ → B₀} {f₁ : A₁ → B₁} {f₂ : A₂ → B₂}
  {hA : A₀ → A₁} {hB : B₀ → B₁}
  {kG : A₁ → A₂} {kH : B₁ → B₂}
  → CommSquare f₀ f₁ hA hB
  → CommSquare f₁ f₂ kG kH
  → CommSquare f₀ f₂ (kG ∘ hA) (kH ∘ hB)
CommSquare-∘h {hA = hA} {kH = kH} (comm-sqr □₀₁) (comm-sqr □₁₂) =
  comm-sqr λ a₀ → ap kH (□₀₁ a₀) ∙ □₁₂ (hA a₀)

CommSquare-inverse : ∀ {i₀ i₁ j₀ j₁}
  {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
  {f₀ : A₀ → B₀} {f₁ : A₁ → B₁} {hA : A₀ → A₁} {hB : B₀ → B₁}
  → CommSquare f₀ f₁ hA hB → (hA-ise : is-equiv hA) (hB-ise : is-equiv hB)
  → CommSquare f₁ f₀ (is-equiv.g hA-ise) (is-equiv.g hB-ise)
CommSquare-inverse {f₀ = f₀} {f₁} {hA} {hB} (comm-sqr f₀□f₁) hA-ise hB-ise =
  comm-sqr λ a₁ → ap (hB.g ∘ f₁) (! $ hA.f-g a₁) ∙ ap hB.g (! $ f₀□f₁ (hA.g a₁)) ∙ hB.g-f (f₀ (hA.g a₁))
  where module hA = is-equiv hA-ise
        module hB = is-equiv hB-ise

is-comm-square-equiv : ∀ {i₀ i₁ j₀ j₁}
  {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
  {f₀ : A₀ → B₀} {f₁ : A₁ → B₁} {hA : A₀ → A₁} {hB : B₀ → B₁}
  → CommSquare f₀ f₁ hA hB → Type (lmax (lmax i₀ i₁) (lmax j₀ j₁))
is-comm-square-equiv {hA = hA} {hB} _ = is-equiv hA × is-equiv hB
