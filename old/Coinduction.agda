{-# OPTIONS --without-K #-}

module Coinduction where

infix 1000 ♯_

postulate
  ∞  : ∀ {i} (A : Set i) → Set i
  ♯_ : ∀ {i} {A : Set i} → A → ∞ A
  ♭  : ∀ {i} {A : Set i} → ∞ A → A

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}
