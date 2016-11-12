{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.TLevel

module experimental.Category where

record CategoryStructure {i j} (Obj : Type i)
  (Mor : Obj → Obj → Type j) : Type (lmax i j) where
  constructor category-structure
  field
    comp : {o₁ o₂ o₃ : Obj} → Mor o₁ o₂ → Mor o₂ o₃ → Mor o₁ o₃
    idm : {o : Obj} → Mor o o
    unit-r : ∀ {o₁ o₂} (m : Mor o₁ o₂) → comp m idm == m
    unit-l : ∀ {o₁ o₂} (m : Mor o₁ o₂) → comp idm m == m

record Category i j : Type (lsucc (lmax i j)) where
  constructor category
  field
    Obj : Type i
    Mor : Obj → Obj → Type j
    Mor-level : ∀ {o₁ o₂} → is-set (Mor o₁ o₂)
    cat-struct : CategoryStructure Obj Mor
  open CategoryStructure cat-struct public
