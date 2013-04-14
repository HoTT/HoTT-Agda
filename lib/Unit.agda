{-# OPTIONS --without-K #-}

module lib.Unit where

open import lib.Base
open import lib.NType
open import lib.TLevel

record ⊤ {i} : Type i where
  constructor tt

Unit = ⊤
Unit₀ = ⊤ {zero}
Unit0 = ⊤ {zero}
⊤₀ = ⊤ {zero}
⊤0 = ⊤ {zero}

module _ {i} where
  private
    U = Unit {i}

  abstract
    -- Unit is contractible
    Unit-is-contr : is-contr U
    Unit-is-contr = (tt , λ y → idp)

    Unit-has-level : (n : ℕ₋₂) → has-level n U
    Unit-has-level n = contr-has-level n Unit-is-contr

    -- [Unit-has-level#instance] produces unsolved metas
    Unit-has-level-S#instance : {n : ℕ₋₂} → has-level (S n) U
    Unit-has-level-S#instance = contr-has-level _ Unit-is-contr

    Unit-is-prop : is-prop U
    Unit-is-prop = Unit-has-level ⟨-1⟩

    Unit-is-set : is-set U
    Unit-is-set = Unit-has-level ⟨0⟩
