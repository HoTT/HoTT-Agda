{-# OPTIONS --without-K #-}

open import lib.Basics

module lib.types.Lift where

lift-equiv : ∀ {i j} {A : Type i} → Lift {j = j} A ≃ A
lift-equiv = equiv lower lift (λ _ → idp) (λ _ → idp)
