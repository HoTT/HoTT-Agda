{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.types.Span
open import lib.types.Pointed
open import lib.types.Pushout

module lib.types.Join  where

module _ {i j} (A : Type i) (B : Type j) where

  *-span : Span
  *-span = span A B (A × B) fst snd

  _*_ : Type _
  _*_ = Pushout *-span

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  ptd-*-span : Ptd-Span
  ptd-*-span = ptd-span X Y (X ×ptd Y) ptd-fst ptd-snd

  _∙*_ : Ptd _
  _∙*_ = Ptd-Pushout ptd-*-span
