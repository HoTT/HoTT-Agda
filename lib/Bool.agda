{-# OPTIONS --without-K #-}

module lib.Bool where

open import lib.Base

data Bool {i} : Type i where
  true : Bool
  false : Bool

Bool₀ = Bool {zero}
Bool0 = Bool {zero}

if_then_else_ : ∀ {i j} {A : Bool {i} → Type j}
  (b : Bool) (t : A true) (e : A false)
  → A b
if true then t else e = t
if false then t else e = e
