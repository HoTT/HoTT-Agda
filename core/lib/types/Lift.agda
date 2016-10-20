{-# OPTIONS --without-K #-}

open import lib.Basics

module lib.types.Lift where

⊙Lift : ∀ {i j} → Ptd i → Ptd (lmax i j)
⊙Lift {j = j} (A , a) =  ⊙[ Lift {j = j} A , lift a ]

⊙lift : ∀ {i j} {X : Ptd i} → X ⊙→ ⊙Lift {j = j} X
⊙lift = (lift , idp)

⊙lower : ∀ {i j} {X : Ptd i} → ⊙Lift {j = j} X ⊙→ X
⊙lower = (lower , idp)

lift-equiv : ∀ {i j} {A : Type i} → A ≃ Lift {j = j} A
lift-equiv = equiv lift lower (λ _ → idp) (λ _ → idp)

-- [lower-equiv] is in Equivalences.agda

Lift-level : ∀ {i j} {A : Type i} {n : ℕ₋₂} →
  has-level n A → has-level n (Lift {j = j} A)
Lift-level = equiv-preserves-level lift-equiv

⊙lift-equiv : ∀ {i j} {X : Ptd i} → X ⊙≃ ⊙Lift {j = j} X
⊙lift-equiv = (⊙lift , snd lift-equiv)

⊙lower-equiv : ∀ {i j} {X : Ptd i} → ⊙Lift {j = j} X ⊙≃ X
⊙lower-equiv = (⊙lower , snd lower-equiv)
