{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.SuspProduct
open import homotopy.SuspSmash
open import homotopy.JoinSusp
open import cohomology.Theory

module cohomology.SphereProduct {i} (CT : CohomologyTheory i)
  (n : ℤ) (m : ℕ) (X : Ptd i) where

  open CohomologyTheory CT
  open import cohomology.Wedge CT

  private
    space-eq : ⊙Susp (⊙Sphere m ⊙× X)
            ⊙≃ ⊙Sphere (S m) ⊙∨ (⊙Susp X ⊙∨ ⊙Susp^ (S m) X)
    space-eq =
      ⊙∨-emap (⊙ide (⊙Sphere (S m)))
        (⊙∨-emap (⊙ide (⊙Susp X))
          (⊙*-Sphere-l m X ⊙∘e SuspSmash.⊙eq (⊙Sphere m) X))
      ⊙∘e SuspProduct.⊙eq (⊙Sphere m) X

  C-Sphere× : C n (⊙Sphere m ⊙× X)
           ≃ᴳ C n (⊙Lift (⊙Sphere m)) ×ᴳ (C n X ×ᴳ C n (⊙Susp^ m X))
  C-Sphere× =
    C n (⊙Sphere m ⊙× X)
      ≃ᴳ⟨ C-Susp n (⊙Sphere m ⊙× X) ⁻¹ᴳ ⟩
    C (succ n) (⊙Susp (⊙Sphere m ⊙× X))
      ≃ᴳ⟨ C-emap (succ n) (space-eq ⊙⁻¹) ⟩
    C (succ n) (⊙Sphere (S m) ⊙∨ (⊙Susp X ⊙∨ ⊙Susp^ (S m) X))
      ≃ᴳ⟨ C-emap (succ n) (⊙∨-emap (⊙Susp-emap (⊙lower-equiv {X = ⊙Sphere m})) (⊙ide _)) ⟩
    C (succ n) (⊙Susp (⊙Lift {j = i} (⊙Sphere m)) ⊙∨ (⊙Susp X ⊙∨ ⊙Susp^ (S m) X))
      ≃ᴳ⟨ C-Wedge (succ n) (⊙Susp (⊙Lift (⊙Sphere m))) (⊙Susp X ⊙∨ ⊙Susp^ (S m) X) ⟩
    C (succ n) (⊙Susp (⊙Lift (⊙Sphere m))) ×ᴳ C (succ n) (⊙Susp X ⊙∨ ⊙Susp^ (S m) X)
      ≃ᴳ⟨ ×ᴳ-emap (C-Susp n (⊙Lift (⊙Sphere m)))
              ( ×ᴳ-emap (C-Susp n X) (C-Susp n (⊙Susp^ m X))
            ∘eᴳ C-Wedge (succ n) (⊙Susp X) (⊙Susp^ (S m) X)) ⟩
    C n (⊙Lift (⊙Sphere m)) ×ᴳ (C n X ×ᴳ C n (⊙Susp^ m X))
      ≃ᴳ∎
