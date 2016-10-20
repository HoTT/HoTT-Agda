{-# OPTIONS --without-K #-}

open import lib.Basics

module lib.types.Empty where

Empty-rec : ∀ {i} {A : Type i} → (Empty → A)
Empty-rec = Empty-elim

⊥-rec : ∀ {i} {A : Type i} → (⊥ → A)
⊥-rec = Empty-rec

abstract
  Empty-is-prop : is-prop Empty
  Empty-is-prop = Empty-elim

  Empty-is-set : is-set Empty
  Empty-is-set = raise-level -1 Empty-is-prop

  Empty-level = Empty-is-prop
  ⊥-is-prop = Empty-is-prop
  ⊥-is-set = Empty-is-set
  ⊥-level = Empty-level
