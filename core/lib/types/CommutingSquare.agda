{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Sigma

module lib.types.CommutingSquare where

{- maps between two functions -}

infix 0 _□$_
_□$_ = CommSquare.commutes

CommSquare-∘v : ∀ {i₀ i₁ i₂ j₀ j₁ j₂}
  {A₀ : Type i₀} {A₁ : Type i₁} {A₂ : Type i₂}
  {B₀ : Type j₀} {B₁ : Type j₁} {B₂ : Type j₂}
  {f₀ : A₀ → B₀} {f₁ : A₁ → B₁} {f₂ : A₂ → B₂}
  {hA : A₀ → A₁} {hB : B₀ → B₁}
  {kA : A₁ → A₂} {kB : B₁ → B₂}
  → CommSquare f₀ f₁ hA hB
  → CommSquare f₁ f₂ kA kB
  → CommSquare f₀ f₂ (kA ∘ hA) (kB ∘ hB)
CommSquare-∘v {hA = hA} {kB = kB} (comm-sqr □₀₁) (comm-sqr □₁₂) =
  comm-sqr λ a₀ → ap kB (□₀₁ a₀) ∙ □₁₂ (hA a₀)

CommSquare-inverse-v : ∀ {i₀ i₁ j₀ j₁}
  {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
  {f₀ : A₀ → B₀} {f₁ : A₁ → B₁} {hA : A₀ → A₁} {hB : B₀ → B₁}
  → CommSquare f₀ f₁ hA hB → (hA-ise : is-equiv hA) (hB-ise : is-equiv hB)
  → CommSquare f₁ f₀ (is-equiv.g hA-ise) (is-equiv.g hB-ise)
CommSquare-inverse-v {f₀ = f₀} {f₁} {hA} {hB} (comm-sqr □) hA-ise hB-ise =
  comm-sqr λ a₁ → ap hB.g (! (□ (hA.g a₁) ∙ ap f₁ (hA.f-g a₁))) ∙ hB.g-f (f₀ (hA.g a₁))
  where module hA = is-equiv hA-ise
        module hB = is-equiv hB-ise

postulate -- TODO
  -- 't' for 'top'
  CommSquare-inverse-inv-t : ∀ {i₀ i₁ j₀ j₁}
    {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
    {f₀ : A₀ → B₀} {f₁ : A₁ → B₁} {hA : A₀ → A₁} {hB : B₀ → B₁}
    (cs : CommSquare f₀ f₁ hA hB) (hA-ise : is-equiv hA) (hB-ise : is-equiv hB)
    → ∀ a₁ → (CommSquare-∘v (CommSquare-inverse-v cs hA-ise hB-ise) cs □$ a₁)
          == is-equiv.f-g hB-ise (f₁ a₁) ∙ ! (ap f₁ (is-equiv.f-g hA-ise a₁))

  -- 'b' for 'bottom'
  CommSquare-inverse-inv-b : ∀ {i₀ i₁ j₀ j₁}
    {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
    {f₀ : A₀ → B₀} {f₁ : A₁ → B₁} {hA : A₀ → A₁} {hB : B₀ → B₁}
    (cs : CommSquare f₀ f₁ hA hB) (hA-ise : is-equiv hA) (hB-ise : is-equiv hB)
    → ∀ a₀ → (CommSquare-∘v cs (CommSquare-inverse-v cs hA-ise hB-ise) □$ a₀)
          == is-equiv.g-f hB-ise (f₀ a₀) ∙ ! (ap f₀ (is-equiv.g-f hA-ise a₀))
