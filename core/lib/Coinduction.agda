{-# OPTIONS --without-K --rewriting #-}

open import lib.Base

module lib.Coinduction where

postulate  -- Coinduction
  ∞  : ∀ {i} (A : Type i) → Type i
  ♯_ : ∀ {i} {A : Type i} → A → ∞ A
  ♭  : ∀ {i} {A : Type i} → ∞ A → A

infix 100 ♯_

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}
