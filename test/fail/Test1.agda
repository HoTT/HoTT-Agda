{-# OPTIONS --without-K #-}

open import lib.Base

module test.fail.Test1 where

module _ where

  private
    data #I-aux : Type₀ where
      #zero : #I-aux
      #one : #I-aux

    data #I : Type₀ where
      #i : #I-aux → (Unit → Unit) → #I

  I : Type₀
  I = #I

  zero : I
  zero = #i #zero _

  one : I
  one = #i #one _

  postulate
    seg : zero == one

absurd : zero ≠ one
absurd ()  -- fails
