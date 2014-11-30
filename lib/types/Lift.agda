{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Pointed

module lib.types.Lift where

⊙Lift : ∀ {i j} → Ptd i → Ptd (lmax i j)
⊙Lift {j = j} (A , a) =  ⊙[ Lift {j = j} A , lift a ]

⊙lift : ∀ {i j} {X : Ptd i} → fst (X ⊙→ ⊙Lift {j = j} X)
⊙lift = (lift , idp)

⊙lower : ∀ {i j} {X : Ptd i} → fst (⊙Lift {j = j} X ⊙→ X)
⊙lower = (lower , idp)

Lift-level : ∀ {i j} {A : Type i} {n : ℕ₋₂} →
  has-level n A → has-level n (Lift {j = j} A)
Lift-level = equiv-preserves-level ((lift-equiv)⁻¹)
