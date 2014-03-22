{-# OPTIONS --without-K #-}

module HoTT where

open import lib.Basics public
open import lib.types.Types public
open import lib.groups.Groups public
open import lib.NType2 public
open import lib.Equivalences2 public
open import lib.NConnected public

{-
To use coinduction in the form of [∞], [♭] and [♯] you can do:

open import HoTT
open Coinduction

You can also use coinductive records and copatterns instead, that’s prettier
(see experimental/GlobularTypes.agda for an example)
-}
module Coinduction where
  open import lib.Coinduction public
