{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Lift
open import lib.types.Paths
open import lib.types.Pointed

module lib.types.Unit where

tt = unit

⊙Unit : Ptd₀
⊙Unit = ⊙[ Unit , unit ]

abstract
  -- Unit is contractible
  Unit-is-contr : is-contr Unit
  Unit-is-contr = (unit , λ y → idp)

  Unit-has-level : {n : ℕ₋₂} → has-level n Unit
  Unit-has-level = contr-has-level Unit-is-contr

  -- [Unit-has-level#instance] produces unsolved metas
  Unit-has-level-S#instance : {n : ℕ₋₂} → has-level (S n) Unit
  Unit-has-level-S#instance = contr-has-level Unit-is-contr

  Unit-is-prop : is-prop Unit
  Unit-is-prop = Unit-has-level

  Unit-is-set : is-set Unit
  Unit-is-set = Unit-has-level

Unit-level = Unit-is-contr
⊤-is-contr = Unit-is-contr
⊤-level = Unit-is-contr
⊤-has-level = Unit-has-level
⊤-is-prop = Unit-is-prop
⊤-is-set = Unit-is-set

LiftUnit-⊙in-level : ∀ {i j} {X : Ptd i}
  → is-contr (fst (X ⊙→ ⊙Lift {j = j} ⊙Unit))
LiftUnit-⊙in-level {X = X} =
  (⊙cst {X = X} ,
   λ f → pair= idp
           (prop-has-all-paths ((Lift-level Unit-is-set) _ _) idp (snd f)))

LiftUnit-⊙out-level : ∀ {i j} {X : Ptd i}
  → is-contr (fst (⊙Lift {j = j} ⊙Unit ⊙→ X))
LiftUnit-⊙out-level {X = X} =
  (⊙cst {Y = X} ,
   λ f → ⊙λ= (λ _ → ! (snd f)) (! (!-inv-l (snd f))))
