{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Cofiber
open import lib.types.Pointed
open import lib.types.PointedSigma
open import lib.types.Wedge

module lib.types.Smash {i j} (X : Ptd i) (Y : Ptd j) where

module ∨In× = WedgeRec {X = X} {Y = Y}
  (λ x → (x , snd Y)) (λ y → (snd X , y)) idp

∨-in-× = ∨In×.f

∨-⊙in-× : X ⊙∨ Y ⊙→ X ⊙× Y
∨-⊙in-× = (∨In×.f , idp)

⊙Smash : Ptd (lmax i j)
⊙Smash = ⊙Cof ∨-⊙in-×

Smash = fst ⊙Smash

_∧_ = Smash
_⊙∧_ = ⊙Smash
