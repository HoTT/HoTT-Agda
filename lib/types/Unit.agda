{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Group
open import lib.types.Lift

module lib.types.Unit where

⊤ = Unit
tt = unit

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

