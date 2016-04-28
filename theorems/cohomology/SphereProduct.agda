{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.SuspProduct
open import homotopy.SuspSmash
open import homotopy.JoinSusp
open import cohomology.Theory

module cohomology.SphereProduct {i} (CT : CohomologyTheory i) where

open CohomologyTheory CT
open import cohomology.Wedge CT

module _ (n : ℤ) (m : ℕ) (X : Ptd i) where

  private

    space-path : ⊙Susp (⊙Sphere {i} m ⊙× X)
              == ⊙Sphere {i} (S m) ⊙∨ (⊙Susp X ⊙∨ ⊙Susp^ (S m) X)
    space-path =
      SuspProduct.⊙path (⊙Sphere m) X
      ∙ ap (λ Z → ⊙Sphere (S m) ⊙∨ (⊙Susp X ⊙∨ Z))
           (SuspSmash.⊙path (⊙Sphere m) X
            ∙ ⊙join-sphere X m)

  C-Sphere× : C n (⊙Sphere {i} m ⊙× X)
           == C n (⊙Sphere m) ×ᴳ (C n X ×ᴳ C n (⊙Susp^ m X))
  C-Sphere× =
    ! (group-ua (C-Susp n (⊙Sphere m ⊙× X)))
    ∙ ap (C (succ n)) space-path
    ∙ CWedge.path (succ n) (⊙Sphere (S m)) (⊙Susp X ⊙∨ ⊙Susp^ (S m) X)
    ∙ ap (λ H → C (succ n) (⊙Sphere (S m)) ×ᴳ H)
         (CWedge.path (succ n) (⊙Susp X) (⊙Susp^ (S m) X)
          ∙ ap2 _×ᴳ_ (group-ua (C-Susp n X))
                     (group-ua (C-Susp n (⊙Susp^ m X))))
    ∙ ap (λ H → H ×ᴳ (C n X ×ᴳ C n (⊙Susp^ m X)))
         (group-ua (C-Susp n (⊙Sphere m)))
