{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.SuspSectionDecomp
open import homotopy.CofiberComp

module homotopy.SuspProduct where

module SuspProduct {i} {j} (X : Ptd i) (Y : Ptd j) where

  private
    i₁ : X ⊙→ X ⊙× Y
    i₁ = ((λ x → (x , snd Y)) , idp)

    i₂ : Y ⊙→ X ⊙× Y
    i₂ = ((λ y → (snd X , y)) , idp)

    j₂ : fst (⊙Cof i₁) → fst Y
    j₂ = CofiberRec.f (snd Y) snd (λ x → idp)

  ⊙eq : ⊙Susp (X ⊙× Y) ⊙≃ ⊙Susp X ⊙∨ (⊙Susp Y ⊙∨ ⊙Susp (X ⊙∧ Y))
  ⊙eq =
    ⊙∨-emap (⊙ide (⊙Susp X))
      (⊙∨-emap (⊙ide (⊙Susp Y))
        (⊙Susp-emap (CofiberComp.⊙eq i₁ i₂)))
    ⊙∘e ⊙∨-emap (⊙ide (⊙Susp X))
        (≃-to-⊙≃ (SuspSectionDecomp.eq (⊙cfcod' i₁ ⊙∘ i₂) j₂ (λ y → idp))
                 (! $ ap winl $ merid (snd Y)))
    ⊙∘e ≃-to-⊙≃ (SuspSectionDecomp.eq i₁ fst (λ x → idp))
                (! $ ap winl $ merid (snd X))
