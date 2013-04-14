{-# OPTIONS --without-K #-}

module lib.Lift where

open import lib.Base

record ↑ {i} (j : ULevel) (A : Type i) : Type (max i j) where
  constructor lift
  field
    ↓ : A
open ↑ public
