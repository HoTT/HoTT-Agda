{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Group
open import lib.types.Unit
open import lib.types.Lift

module lib.groups.Unit where

LiftUnit-group-structure : ∀ {i} → GroupStructure {i} (Lift Unit) 
LiftUnit-group-structure = record
  { ident = lift unit
  ; inv = λ _ → lift unit
  ; comp = λ _ _ → lift unit
  ; unitl = λ _ → idp
  ; unitr = λ _ → idp
  ; assoc = λ _ _ _ → idp
  ; invr = λ _ → idp
  ; invl = λ _ → idp
  }

LiftUnit-Group : ∀ {i} → Group i
LiftUnit-Group = group _ (Lift-level Unit-is-set) LiftUnit-group-structure

contr-iso-LiftUnit : ∀ {i} (G : Group i) → is-contr (Group.El G)
  → G == LiftUnit-Group
contr-iso-LiftUnit G pA = group-iso 
  (group-hom (λ _ → lift unit) idp (λ _ _ → idp)) 
  (snd (contr-equiv-LiftUnit pA))
