{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.HSpace where

record HSpaceStructure {i} (A : Type i) : Type i where
  constructor hSpaceStructure
  field
    e : A
    μ : A → A → A
    μe- : (a : A) → μ e a == a
    μ-e : (a : A) → μ a e == a
