{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Cospan

module lib.types.Pullback where

module _ {i j k} (D : Cospan {i} {j} {k}) where

  open Cospan D

  record Pullback : Type (lmax i (lmax j k)) where
    constructor pullback
    field
      a : A
      b : B
      h : f a == g b

  pullback= : {a a' : A} (p : a == a') {b b' : B} (q : b == b')
    {h : f a == g b} {h' : f a' == g b'} (r : h ∙ ap g q == ap f p ∙ h')
    → pullback a b h == pullback a' b' h'
  pullback= idp idp r =
    ap (pullback _ _) (! (∙-unit-r _) ∙ r)

open Pullback
