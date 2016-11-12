{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Paths

module lib.types.Unit where

pattern tt = unit

⊙Unit : Ptd₀
⊙Unit = ⊙[ Unit , unit ]

abstract
  -- Unit is contractible
  Unit-is-contr : is-contr Unit
  Unit-is-contr = (unit , λ y → idp)

  Unit-is-prop : is-prop Unit
  Unit-is-prop = raise-level -2 Unit-is-contr

  Unit-is-set : is-set Unit
  Unit-is-set = raise-level -1 Unit-is-prop

  Unit-level = Unit-is-contr
  ⊤-is-contr = Unit-is-contr
  ⊤-level = Unit-is-contr
  ⊤-is-prop = Unit-is-prop
  ⊤-is-set = Unit-is-set
