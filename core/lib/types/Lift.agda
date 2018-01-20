{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

module lib.types.Lift where

⊙Lift : ∀ {i j} → Ptd i → Ptd (lmax i j)
⊙Lift {j = j} ⊙[ A , a ] =  ⊙[ Lift {j = j} A , lift a ]

⊙lift : ∀ {i j} {X : Ptd i} → X ⊙→ ⊙Lift {j = j} X
⊙lift = (lift , idp)

⊙lower : ∀ {i j} {X : Ptd i} → ⊙Lift {j = j} X ⊙→ X
⊙lower = (lower , idp)

lift-equiv : ∀ {i j} {A : Type i} → A ≃ Lift {j = j} A
lift-equiv = equiv lift lower (λ _ → idp) (λ _ → idp)

-- [lower-equiv] is in Equivalences.agda

instance
  Lift-level : ∀ {i j} {A : Type i} {n : ℕ₋₂}
    → has-level n A → has-level n (Lift {j = j} A)
  Lift-level p = equiv-preserves-level lift-equiv {{p}}

⊙lift-equiv : ∀ {i j} {X : Ptd i} → X ⊙≃ ⊙Lift {j = j} X
⊙lift-equiv = (⊙lift , snd lift-equiv)

⊙lower-equiv : ∀ {i j} {X : Ptd i} → ⊙Lift {j = j} X ⊙≃ X
⊙lower-equiv = (⊙lower , snd lower-equiv)

Lift-fmap : ∀ {i j k} {A : Type i} {B : Type j}
  → (A → B) → (Lift {j = k} A → Lift {j = k} B)
Lift-fmap f = lift ∘ f ∘ lower

Lift-fmap-equiv : ∀ {i j k} {A : Type i} {B : Type j}
  → (A → B) ≃ (Lift {j = k} A → Lift {j = k} B)
Lift-fmap-equiv = equiv Lift-fmap (λ f → lower ∘ f ∘ lift) (λ _ → idp) (λ _ → idp)

⊙Lift-fmap : ∀ {i j k} {X : Ptd i} {Y : Ptd j}
  → (X ⊙→ Y) → (⊙Lift {j = k} X ⊙→ ⊙Lift {j = k} Y)
⊙Lift-fmap f = ⊙lift ⊙∘ f ⊙∘ ⊙lower

⊙Lift-fmap-equiv : ∀ {i j k} {X : Ptd i} {Y : Ptd j}
  → (X ⊙→ Y) ≃ (⊙Lift {j = k} X ⊙→ ⊙Lift {j = k} Y)
⊙Lift-fmap-equiv = equiv ⊙Lift-fmap (λ f → ⊙lower ⊙∘ f ⊙∘ ⊙lift)
  (λ {(_ , idp) → idp}) (λ {(_ , idp) → idp})
