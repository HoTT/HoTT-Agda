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

Lift-Unit-group-structure : ∀ {i} → 
  GroupStructure {i} (Lift Unit) 
Lift-Unit-group-structure = record
  { ident = lift unit
  ; inv = λ _ → lift unit
  ; comp = λ _ _ → lift unit
  ; unitl = λ _ → idp
  ; unitr = λ _ → idp
  ; assoc = λ _ _ _ → idp
  ; invr = λ _ → idp
  ; invl = λ _ → idp
  }

LiftUnit-group : ∀ {i} → Group i
LiftUnit-group = group _ (Lift-level Unit-is-set) Lift-Unit-group-structure

contr-iso-LiftUnit : ∀ {i} (G : Group i) → is-contr (Group.El G)
  → G == LiftUnit-group
contr-iso-LiftUnit G pA = group-iso 
  (group-hom (λ _ → lift unit) idp (λ _ _ → idp)) 
  (snd (contr-equiv-LiftUnit pA))