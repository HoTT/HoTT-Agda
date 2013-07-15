{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.types.Span
open import lib.types.Pushout

module lib.types.Join {i j} (A : Type i) (B : Type j) where

*-span : Span
*-span = span A B (A × B) fst snd

_*_ : Type _
_*_ = Pushout *-span
