{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Paths

module lib.types.Unit where

pattern tt = unit

⊙Unit : Ptd₀
⊙Unit = ⊙[ Unit , unit ]

-- Unit is contractible
instance
  Unit-level : {n : ℕ₋₂} → has-level n Unit
  Unit-level {n = ⟨-2⟩} = has-level-in (unit , λ y → idp)
  Unit-level {n = S n} = raise-level n Unit-level
