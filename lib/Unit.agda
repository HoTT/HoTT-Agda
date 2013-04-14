{-# OPTIONS --without-K #-}

module lib.Unit where

open import lib.Base

record ⊤ {i} : Type i where
  constructor tt

Unit = ⊤
Unit₀ = ⊤ {zero}
Unit0 = ⊤ {zero}
⊤₀ = ⊤ {zero}
⊤0 = ⊤ {zero}
