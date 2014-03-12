{-# OPTIONS --without-K #-}

open import lib.Base

module test.succeed.Test1 where

module _ where

  private
    data #I : Type₀ where
      #zero : #I
      #one : #I

  I : Type₀
  I = #I

  zero : I
  zero = #zero

  one : I
  one = #one

  postulate
    seg : zero == one

absurd : zero ≠ one
absurd ()
