{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Cofiber
open import lib.types.Pointed
open import lib.types.Wedge

module lib.types.Smash {i j} (X : Ptd i) (Y : Ptd j) where

module ∨In× = WedgeRec {X = X} {Y = Y}
  (λ x → (x , snd Y)) (λ y → (snd X , y)) idp

∨-in-× : fst (Ptd-Wedge X Y ∙→ X ×ptd Y)
∨-in-× = (∨In×.f , idp)

Ptd-Smash : Ptd (lmax i j)
Ptd-Smash = Ptd-Cof ∨-in-×

Smash = fst Ptd-Smash
