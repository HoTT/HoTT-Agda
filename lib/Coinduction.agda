{-# OPTIONS --without-K #-}

open import lib.Base

module lib.Coinduction where

infix 1000 ♯_

postulate  -- Coinduction
  ∞  : ∀ {i} (A : Type i) → Type i
  ♯_ : ∀ {i} {A : Type i} → A → ∞ A
  ♭  : ∀ {i} {A : Type i} → ∞ A → A

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}
