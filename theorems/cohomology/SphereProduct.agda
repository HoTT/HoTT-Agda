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

    space-path : ⊙Susp (⊙Lift {j = i} (⊙Sphere m) ⊙× X)
              == ⊙Susp (⊙Lift (⊙Sphere m)) ⊙∨ (⊙Susp X ⊙∨ ⊙Susp^ (S m) X)
    space-path =
      SuspProduct.⊙path (⊙Lift (⊙Sphere m)) X
      ∙ ap (λ Z → ⊙Susp (⊙Lift (⊙Sphere m)) ⊙∨ (⊙Susp X ⊙∨ Z))
           (SuspSmash.⊙path (⊙Lift (⊙Sphere m)) X
            ∙ ⊙*-⊙Lift-⊙Sphere m X)

  C-Sphere× : C n (⊙Lift {j = i} (⊙Sphere m) ⊙× X)
           == C n (⊙Lift (⊙Sphere m)) ×ᴳ (C n X ×ᴳ C n (⊙Susp^ m X))
  C-Sphere× =
    ! (group-ua (C-Susp n (⊙Lift {j = i} (⊙Sphere m) ⊙× X)))
    ∙ ap (C (succ n)) space-path
    ∙ CWedge.path (succ n) (⊙Susp (⊙Lift (⊙Sphere m))) (⊙Susp X ⊙∨ ⊙Susp^ (S m) X)
    ∙ ap (λ H → C (succ n) (⊙Susp (⊙Lift (⊙Sphere m))) ×ᴳ H)
         (CWedge.path (succ n) (⊙Susp X) (⊙Susp^ (S m) X)
          ∙ ap2 _×ᴳ_ (group-ua (C-Susp n X))
                     (group-ua (C-Susp n (⊙Susp^ m X))))
    ∙ ap (λ H → H ×ᴳ (C n X ×ᴳ C n (⊙Susp^ m X)))
         (group-ua (C-Susp n (⊙Lift (⊙Sphere m))))
