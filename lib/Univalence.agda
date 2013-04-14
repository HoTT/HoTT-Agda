{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.Equivalences

module lib.Univalence where

postulate  -- Univalence axiom
  ua : ∀ {i} {A B : Type i} → (A ≃ B) → A == B
