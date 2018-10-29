{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.CupProduct.OnEM.InAllDegrees
open import cohomology.EMModel
open import cohomology.Theory
open import homotopy.EilenbergMacLane

module cohomology.CupProduct.Definition {i} (X : Ptd i) where

private
  module M {k} (A : AbGroup k) = CohomologyTheory (EM-Cohomology A)
  open M

smin-map : ∀ {j k} {Y : Ptd j} {Z : Ptd k}
  → X ⊙→ Y
  → X ⊙→ Z
  → X ⊙→ Y ⊙∧ Z
smin-map f g = (λ x → smin (fst f x) (fst g x)) , ap2 smin (snd f) (snd g)

module _ (G : AbGroup i) (H : AbGroup i) where

  private
    module G⊗H = TensorProduct G H
  open EMExplicit

  private
    ⊙Ω∧-cp : ∀ {m n : ℕ} → ⊙Ω (⊙EM G (S m)) ⊙∧ ⊙Ω (⊙EM H (S n)) ⊙→ ⊙Ω (⊙EM G⊗H.abgroup (S (m + n)))
    ⊙Ω∧-cp {m} {n} =
      ⊙<– (spectrum G⊗H.abgroup (m + n)) ⊙∘
      ⊙∧-cp G H m n ⊙∘
      ⊙∧-fmap (⊙–> (spectrum G m)) (⊙–> (spectrum H n))

  _∪_  : ∀ {m n : ℕ} → CEl G (pos m) X → CEl H (pos n) X → CEl G⊗H.abgroup (pos (m + n)) X
  _∪_ s t = Trunc-rec (λ s' → Trunc-rec (λ t' → [ ⊙Ω∧-cp ⊙∘ smin-map s' t' ]) t) s

  -- ∪-hom : ∀ {m n : ℕ} → TensorProduct.grp (C-abgroup G (pos m) X) (C-abgroup H (pos n) X) →ᴳ C G⊗H.abgroup (pos (m + n)) X
  -- ∪-hom = {!!}
