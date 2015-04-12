{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.SuspSectionDecomp
open import homotopy.CofiberComp

module homotopy.SuspProduct where

module SuspProduct {i} {j} (X : Ptd i) (Y : Ptd j) where

  private
    i₁ : fst (X ⊙→ X ⊙× Y)
    i₁ = ((λ x → (x , snd Y)) , idp)

    i₂ : fst (Y ⊙→ X ⊙× Y)
    i₂ = ((λ y → (snd X , y)) , idp)

    j₂ : fst (⊙Cof i₁) → fst Y
    j₂ = CofiberRec.f _ (snd Y) snd (λ x → idp)

  ⊙path : ⊙Susp (X ⊙× Y) == ⊙Susp X ⊙∨ (⊙Susp Y ⊙∨ ⊙Susp (X ⊙∧ Y))
  ⊙path =
    ⊙ua (⊙ify-eq (SuspSectionDecomp.eq i₁ fst (λ x → idp))
                 (! $ ap winl $ merid _ (snd X)))
    ∙ ap (λ Z → ⊙Susp X ⊙∨ Z)
         (⊙ua (⊙ify-eq (SuspSectionDecomp.eq (⊙cfcod i₁ ⊙∘ i₂) j₂ (λ y → idp))
                       (! $ ap winl $ merid _ (snd Y))))
    ∙ ap (λ Z → ⊙Susp X ⊙∨ (⊙Susp Y ⊙∨ ⊙Susp Z))
         (CofiberComp.⊙path i₁ i₂)
