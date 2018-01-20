{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.SphereEndomorphism
open import groups.Pointed
open import groups.SphereEndomorphism
open import groups.FromSusp
open import cohomology.Theory

module cohomology.SphereEndomorphism {i} (CT : CohomologyTheory i) (n : ℤ) (m : ℕ) where

  open CohomologyTheory CT
  open import cohomology.Cogroup CT n
    (Lift-Susp-cogroup-structure (⊙Sphere m))
    (⊙Lift {j = i} (⊙Sphere (S m)))
  
  C-fmap-hom : Trunc-⊙LiftSphereS-endo-group m →ᴳ
    (hom-group (C n (⊙Lift (⊙Sphere (S m)))) (C-abgroup n (⊙Lift (⊙Sphere (S m)))))
  C-fmap-hom = group-hom
    (Trunc-rec λ f → C-fmap n f)
    (Trunc-elim λ f → Trunc-elim λ g → C-fmap-preserves-comp f g)
