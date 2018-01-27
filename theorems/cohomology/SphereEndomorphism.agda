{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.SphereEndomorphism
open import groups.Pointed
open import groups.SphereEndomorphism
open import groups.FromSusp
open import cohomology.Theory

module cohomology.SphereEndomorphism (CT : CohomologyTheory lzero) (n : ℤ) (m : ℕ) where

  open CohomologyTheory CT
  open import cohomology.Cogroup CT n
    (Susp-cogroup-structure (⊙Sphere m))
    (⊙Sphere (S m))
  
  private
    C-fmap' : Trunc-⊙Sphere-endo (S m) → (C n (⊙Sphere (S m)) →ᴳ C n (⊙Sphere (S m)))
    C-fmap' = Trunc-rec λ f → C-fmap n f

    CEl-fmap' : Trunc-⊙Sphere-endo (S m) → (CEl n (⊙Sphere (S m)) → CEl n (⊙Sphere (S m)))
    CEl-fmap' f = GroupHom.f (C-fmap' f)

    C-fmap'-hom : Trunc-⊙SphereS-endo-group m →ᴳ
      (hom-group (C n (⊙Sphere (S m))) (C-abgroup n (⊙Sphere (S m))))
    C-fmap'-hom = group-hom C-fmap'
      (Trunc-elim λ f → Trunc-elim λ g → C-fmap-preserves-comp f g)

    CEl-fmap'-η : ∀ (f : Trunc-⊙Sphere-endo (S m)) (g : CEl n (⊙Sphere (S m)))
      → CEl-fmap' f g == Group.exp (C n (⊙Sphere (S m))) g (Trunc-⊙SphereS-endo-degree m f)
    CEl-fmap'-η f g =
      CEl-fmap' f g
        =⟨ ! $ ap (λ f → CEl-fmap' f g) $ is-equiv.f-g (Trunc-⊙SphereS-endo-⊙group-is-infinite-cyclic m) f ⟩
      CEl-fmap' (Group.exp (Trunc-⊙SphereS-endo-group m) [ ⊙idf _ ] (Trunc-⊙SphereS-endo-degree m f)) g
        =⟨ GroupHom.pres-exp
            (app-hom g ∘ᴳ C-fmap'-hom)
            [ ⊙idf _ ]
            (Trunc-⊙SphereS-endo-degree m f) ⟩
      Group.exp
        (C n (⊙Sphere (S m)))
        (CEl-fmap' [ ⊙idf _ ] g)
        (Trunc-⊙SphereS-endo-degree m f)
        =⟨ ap (λ g → Group.exp (C n (⊙Sphere (S m))) g (Trunc-⊙SphereS-endo-degree m f)) $
              CEl-fmap-idf n g  ⟩
      Group.exp
        (C n (⊙Sphere (S m))) g
        (Trunc-⊙SphereS-endo-degree m f)
        =∎
  abstract
    CEl-fmap-⊙Sphere-endo-η : ∀ (f : ⊙Sphere-endo (S m)) (g : CEl n (⊙Sphere (S m)))
      → CEl-fmap n f g == Group.exp (C n (⊙Sphere (S m))) g (⊙SphereS-endo-degree m f)
    CEl-fmap-⊙Sphere-endo-η f = CEl-fmap'-η [ f ]
