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
              == ⊙Sphere {i} (S m) ⊙∨ (⊙Susp^ (S m) X ⊙∨ ⊙Susp X)
    space-path =
      SuspProduct.⊙path (⊙Sphere m) X
      ∙ ap (λ Z → ⊙Sphere (S m) ⊙∨ (Z ⊙∨ ⊙Susp X))
           (SuspSmash.⊙path (⊙Sphere m) X
            ∙ ⊙join-sphere X m)

  C-Sphere× : C n (⊙Sphere {i} m ⊙× X)
           == C n (⊙Sphere m) ×G (C n (⊙Susp^ m X) ×G C n X)
  C-Sphere× =
    ! (C-Susp n (⊙Sphere m ⊙× X))
    ∙ ap (C (succ n)) space-path
    ∙ C-binary-additive (succ n) (⊙Sphere (S m)) (⊙Susp^ (S m) X ⊙∨ ⊙Susp X)
    ∙ ap (λ H → C (succ n) (⊙Sphere (S m)) ×G H)
         (C-binary-additive (succ n) (⊙Susp^ (S m) X) (⊙Susp X)
          ∙ ap2 _×G_ (C-Susp n (⊙Susp^ m X))
                     (C-Susp n X))
    ∙ ap (λ H → H ×G (C n (⊙Susp^ m X) ×G C n X))
         (C-Susp n (⊙Sphere m))
