{-# OPTIONS --without-K #-}

open import HoTT

module Reflective where

  record ReflectiveSubuniverse {ℓ} : Type (lsucc ℓ) where
    field

      P : Type ℓ → Type ℓ
      R : Type ℓ → Type ℓ

      η : (A : Type ℓ) → A → R A

      -- replete : (A B : Type ℓ) → P A → A ≃ B → P B
      
