{-# OPTIONS --without-K #-}

module HoTT where

open import lib.Basics public

open import lib.Equivalence2 public
open import lib.NConnected public
open import lib.NType2 public
open import lib.Relation2 public
open import lib.Function2 public

open import lib.cubical.Cubical public
open import lib.groups.Groups public
open import lib.types.Types public

{-
To use coinduction in the form of [∞], [♭] and [♯] you can do:

open import HoTT
open Coinduction

You can also use coinductive records and copatterns instead, that’s prettier
(see experimental/GlobularTypes.agda for an example)
-}
module Coinduction where
  open import lib.Coinduction public

-- deprecated operators
module _ where
  infix 15 _∎
  _∎ = _=∎
