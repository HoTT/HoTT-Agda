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

  *-⊙span : ⊙Span
  *-⊙span = ⊙span X Y (X ⊙× Y) ⊙fst ⊙snd

  _⊙*_ : Ptd _
  _⊙*_ = ⊙Pushout *-⊙span
