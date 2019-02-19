{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.SuspProduct
open import homotopy.SuspSmashJoin
open import homotopy.JoinSusp
open import cohomology.Theory

module cohomology.SphereProduct {i} (CT : CohomologyTheory i)
  (n : ℤ) (m : ℕ) (X : Ptd i) where

  open CohomologyTheory CT
  open import cohomology.Wedge CT

  private
    space-eq : ⊙Susp (Sphere m × de⊙ X)
            ⊙≃ ⊙Sphere (S m) ⊙∨ (⊙Susp (de⊙ X) ⊙∨ ⊙Susp^ (S m) X)
    space-eq =
      ⊙∨-emap (⊙ide (⊙Sphere (S m)))
        (⊙∨-emap (⊙ide (⊙Susp (de⊙ X)))
          (⊙*-Sphere-l m X ⊙∘e SuspSmashJoin.⊙eq (⊙Sphere m) X))
      ⊙∘e SuspProduct.⊙eq (⊙Sphere m) X

  C-Sphere× : C n (⊙Sphere m ⊙× X)
           ≃ᴳ C n (⊙Lift (⊙Sphere m)) ×ᴳ (C n X ×ᴳ C n (⊙Susp^ m X))
  C-Sphere× =
    C n (⊙Sphere m ⊙× X)
      ≃ᴳ⟨ C-Susp n (⊙Sphere m ⊙× X) ⁻¹ᴳ ⟩
    C (succ n) (⊙Susp (Sphere m × de⊙ X))
      ≃ᴳ⟨ C-emap (succ n) (space-eq ⊙⁻¹) ⟩
    C (succ n) (⊙Sphere (S m) ⊙∨ (⊙Susp (de⊙ X) ⊙∨ ⊙Susp^ (S m) X))
      ≃ᴳ⟨ C-emap (succ n) (⊙∨-emap (⊙Susp-emap (lower-equiv {A = Sphere m})) (⊙ide _)) ⟩
    C (succ n) (⊙Susp (Lift {j = i} (Sphere m)) ⊙∨ (⊙Susp (de⊙ X) ⊙∨ ⊙Susp^ (S m) X))
      ≃ᴳ⟨ C-Wedge (succ n) (⊙Susp (Lift (Sphere m))) (⊙Susp (de⊙ X) ⊙∨ ⊙Susp^ (S m) X) ⟩
    C (succ n) (⊙Susp (Lift (Sphere m))) ×ᴳ C (succ n) (⊙Susp (de⊙ X) ⊙∨ ⊙Susp^ (S m) X)
      ≃ᴳ⟨ ×ᴳ-emap (C-Susp n (⊙Lift (⊙Sphere m)))
              ( ×ᴳ-emap (C-Susp n X) (C-Susp n (⊙Susp^ m X))
            ∘eᴳ C-Wedge (succ n) (⊙Susp (de⊙ X)) (⊙Susp^ (S m) X)) ⟩
    C n (⊙Lift (⊙Sphere m)) ×ᴳ (C n X ×ᴳ C n (⊙Susp^ m X))
      ≃ᴳ∎
