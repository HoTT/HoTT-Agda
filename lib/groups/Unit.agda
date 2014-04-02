{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Group
open import lib.types.Unit
open import lib.groups.Lift

module lib.groups.Unit where

Unit-group-structure : GroupStructure Unit
Unit-group-structure = record
  { ident = unit
  ; inv = λ _ → unit
  ; comp = λ _ _ → unit
  ; unitl = λ _ → idp
  ; unitr = λ _ → idp
  ; assoc = λ _ _ _ → idp
  ; invr = λ _ → idp
  ; invl = λ _ → idp
  }

Unit-Group : Group lzero
Unit-Group = group _ Unit-is-set Unit-group-structure

LiftUnit-Group : ∀ {i} → Group i
LiftUnit-Group = Lift-Group Unit-Group

contr-iso-LiftUnit : ∀ {i} (G : Group i) → is-contr (Group.El G)
  → G == LiftUnit-Group
contr-iso-LiftUnit G pA = group-iso 
  (group-hom (λ _ → lift unit) idp (λ _ _ → idp)) 
  (snd (contr-equiv-LiftUnit pA))
