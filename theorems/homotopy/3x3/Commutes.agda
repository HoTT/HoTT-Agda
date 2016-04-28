{-# OPTIONS --without-K #-}

open import homotopy.3x3.PushoutPushout
open import homotopy.3x3.Transpose
import homotopy.3x3.To as To
import homotopy.3x3.From as From
open import homotopy.3x3.Common

module homotopy.3x3.Commutes {i} (d : Span^2 {i}) where

open Span^2 d
open M using (Pushout^2)

open To d
open From d

open import homotopy.3x3.FromTo
open import homotopy.3x3.ToFrom

abstract
  theorem : Pushout^2 d ≃ Pushout^2 (transpose d)
  theorem = equiv to from (to-from d) (from-to d)