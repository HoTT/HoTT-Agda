{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.SuspSectionDecomp
open import homotopy.CofiberComp
open import homotopy.SmashIsCofiber

module homotopy.SuspProduct where

module SuspProduct {i} {j} (X : Ptd i) (Y : Ptd j) where

  private
    i₁ : X ⊙→ X ⊙× Y
    i₁ = ((λ x → (x , pt Y)) , idp)

    i₂ : Y ⊙→ X ⊙× Y
    i₂ = ((λ y → (pt X , y)) , idp)

    j₂ : de⊙ (⊙Cofiber i₁) → de⊙ Y
    j₂ = CofiberRec.f (pt Y) snd (λ x → idp)

  ⊙eq : ⊙Susp (de⊙ X × de⊙ Y) ⊙≃ ⊙Susp (de⊙ X) ⊙∨ (⊙Susp (de⊙ Y) ⊙∨ ⊙Susp (X ∧ Y))
  ⊙eq =
    ⊙∨-emap (⊙ide (⊙Susp (de⊙ X)))
      (⊙∨-emap (⊙ide (⊙Susp (de⊙ Y)))
        (⊙Susp-emap (Smash-equiv-Cof X Y ⁻¹ ∘e CofiberComp.eq i₁ i₂)))
    ⊙∘e ⊙∨-emap (⊙ide (⊙Susp (de⊙ X)))
          (≃-to-⊙≃ (SuspSectionDecomp.eq (⊙cfcod' i₁ ⊙∘ i₂) j₂ (λ y → idp))
                   (! $ ap winl $ merid (pt Y)))
    ⊙∘e ≃-to-⊙≃ (SuspSectionDecomp.eq i₁ fst (λ x → idp))
                (! $ ap winl $ merid (pt X))
