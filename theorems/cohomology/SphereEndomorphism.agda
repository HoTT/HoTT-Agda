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
  
  C-fmap' : Trunc-⊙LiftSphere-endo (S m) → (C n (⊙Lift (⊙Sphere (S m))) →ᴳ C n (⊙Lift (⊙Sphere (S m))))
  C-fmap' = Trunc-rec λ f → C-fmap n f

  CEl-fmap' : Trunc-⊙LiftSphere-endo (S m) → (CEl n (⊙Lift (⊙Sphere (S m))) → CEl n (⊙Lift (⊙Sphere (S m))))
  CEl-fmap' f = GroupHom.f (C-fmap' f)

  C-fmap'-hom : Trunc-⊙LiftSphereS-endo-group m →ᴳ
    (hom-group (C n (⊙Lift (⊙Sphere (S m)))) (C-abgroup n (⊙Lift (⊙Sphere (S m)))))
  C-fmap'-hom = group-hom C-fmap'
    (Trunc-elim λ f → Trunc-elim λ g → C-fmap-preserves-comp f g)

  abstract
    CEl-fmap'-η : ∀ (f : Trunc-⊙LiftSphere-endo {i} (S m)) (g : CEl n (⊙Lift (⊙Sphere (S m))))
      → CEl-fmap' f g == Group.exp (C n (⊙Lift (⊙Sphere (S m)))) g (Trunc-⊙LiftSphereS-endo-degree {i} m f)
    CEl-fmap'-η f g =
      CEl-fmap' f g
        =⟨ ! $ ap (λ f → CEl-fmap' f g) $ is-equiv.f-g (Trunc-⊙LiftSphereS-endo-⊙group-is-infinite-cyclic {i} m) f ⟩
      CEl-fmap' (Group.exp (Trunc-⊙LiftSphereS-endo-group {i} m) [ ⊙idf _ ] (Trunc-⊙LiftSphereS-endo-degree {i} m f)) g
        =⟨ ap (λ φ → GroupHom.f φ g) $
              GroupHom.pres-exp
              C-fmap'-hom
              [ ⊙idf _ ]
              (Trunc-⊙LiftSphereS-endo-degree {i} m f) ⟩
      GroupHom.f
        (Group.exp
          (hom-group (C n (⊙Lift (⊙Sphere (S m)))) (C-abgroup n (⊙Lift (⊙Sphere (S m)))))
          (C-fmap' [ ⊙idf _ ])
          (Trunc-⊙LiftSphereS-endo-degree {i} m f))
        g
        =⟨ GroupHom.pres-exp
            (app-hom g)
            (C-fmap' [ ⊙idf _ ])
            (Trunc-⊙LiftSphereS-endo-degree {i} m f) ⟩
      Group.exp
        (C n (⊙Lift (⊙Sphere (S m))))
        (CEl-fmap' [ ⊙idf _ ] g)
        (Trunc-⊙LiftSphereS-endo-degree {i} m f)
        =⟨ ap (λ g → Group.exp (C n (⊙Lift (⊙Sphere (S m)))) g (Trunc-⊙LiftSphereS-endo-degree {i} m f)) $
              CEl-fmap-idf n g  ⟩
      Group.exp
        (C n (⊙Lift (⊙Sphere (S m)))) g
        (Trunc-⊙LiftSphereS-endo-degree {i} m f)
        =∎

    CEl-fmap-η : ∀ (f : ⊙LiftSphere-endo {i} (S m)) (g : CEl n (⊙Lift (⊙Sphere (S m))))
      → CEl-fmap n f g == Group.exp (C n (⊙Lift (⊙Sphere (S m)))) g (⊙LiftSphereS-endo-degree {i} m f)
    CEl-fmap-η f = CEl-fmap'-η [ f ]
