{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.SphereEndomorphism
open import groups.Pointed
open import groups.SphereEndomorphism
open import groups.FromSusp
open import cohomology.Theory

module cohomology.SphereEndomorphism {i} (CT : CohomologyTheory i) (n : ℤ) where

  open CohomologyTheory CT
  module CCGS m where
    open import cohomology.Cogroup CT n
      (Lift-Susp-cogroup-structure (⊙Sphere m))
      (⊙Lift {j = i} (⊙Sphere (S m))) public
  
  C-fmap-hom : ∀ m → Trunc-⊙LiftSphereS-endo-group m →ᴳ
    (hom-group (C n (⊙Lift (⊙Sphere (S m)))) (C-abgroup n (⊙Lift (⊙Sphere (S m)))))
  C-fmap-hom m = group-hom
    (Trunc-rec λ f → C-fmap n f)
    (Trunc-elim λ f → Trunc-elim λ g → CCGS.C-fmap-preserves-comp m f g)
