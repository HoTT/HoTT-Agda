{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.LoopSpaceCircle
open import homotopy.SphereEndomorphism
open import homotopy.SuspAdjointLoop
open import groups.FromSusp
open import groups.SuspAdjointLoop

module groups.SphereEndomorphism where

  ⊙SphereS-endo-group-structure : ∀ n → GroupStructure (⊙Sphere (S n) ⊙→ ⊙Sphere (S n))
  ⊙SphereS-endo-group-structure n = Susp⊙→-group-structure (⊙Sphere n) (⊙Sphere (S n))

  Trunc-⊙SphereS-endo-group : ∀ n → Group₀
  Trunc-⊙SphereS-endo-group n = Trunc-group (⊙SphereS-endo-group-structure n)

  Trunc-⊙SphereS-endo-Susp-fmap-iso :
    ∀ n → Trunc-⊙SphereS-endo-group n ≃ᴳ Trunc-⊙SphereS-endo-group (S n)
  Trunc-⊙SphereS-endo-Susp-fmap-iso n =
    Trunc-group-fmap (Susp⊙→-Susp-fmap-hom (⊙Sphere n) (⊙Sphere (S n))) ,
    Trunc-⊙SphereS-endo-Susp-is-equiv n
