{-# OPTIONS --without-K #-}

open import lib.Basics

module lib.types.Bool where

data Bool : Type₀ where
  true : Bool
  false : Bool

if_then_else_ : ∀ {i} {A : Bool → Type i}
  (b : Bool) (t : A true) (e : A false)
  → A b
if true then t else e = t
if false then t else e = e

private
  Bool-true≠false-type : Bool → Type₀
  Bool-true≠false-type true  = Unit
  Bool-true≠false-type false = Empty

abstract
  Bool-true≠false : true ≠ false
  Bool-true≠false p = transport Bool-true≠false-type p unit

  Bool-false≠true : false ≠ true
  Bool-false≠true p = transport Bool-true≠false-type (! p) unit

  Bool-has-dec-eq : has-dec-eq Bool
  Bool-has-dec-eq true true = inl idp
  Bool-has-dec-eq true false = inr Bool-true≠false
  Bool-has-dec-eq false true = inr Bool-false≠true
  Bool-has-dec-eq false false = inl idp

  Bool-is-set : is-set Bool
  Bool-is-set = dec-eq-is-set Bool-has-dec-eq

Bool-level = Bool-is-set
