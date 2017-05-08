{-# OPTIONS --without-K --rewriting #-}

module HoTT where

open import lib.Basics public

open import lib.Equivalence2 public
open import lib.NConnected public
open import lib.NType2 public
open import lib.Relation2 public
open import lib.Function2 public

open import lib.cubical.Cubical public
open import lib.types.Types public
open import lib.groups.Groups public
open import lib.groupoids.Groupoids public
open import lib.modalities.Modalities public

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
  conn-elim = conn-extend
  conn-elim-β = conn-extend-β
  conn-elim-general = conn-extend-general
  conn-intro = conn-in

  if_then_else_ : ∀ {i} {A : Type i}
    → Bool → A → A → A
  if true then t else e = t
  if false then t else e = e
