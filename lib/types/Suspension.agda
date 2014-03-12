{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Span
open import lib.types.Pushout
open import lib.types.PushoutFlattening
open import lib.types.Unit

-- Suspension is defined as a particular case of pushout

module lib.types.Suspension {i} (A : Type i) where

suspension-span : Span
suspension-span = span Unit Unit A (λ _ → tt) (λ _ → tt)

Suspension : Type i
Suspension = Pushout suspension-span

north : Suspension
north = left tt

south : Suspension
south = right tt

merid : A → north == south
merid x = glue x

module SuspensionElim {j} {P : Suspension → Type j} (n : P north) (s : P south)
  (p : (x : A) → n == s [ P ↓ merid x ])
  = PushoutElim (λ _ → n) (λ _ → s) p

open SuspensionElim public using () renaming (f to Suspension-elim)

module SuspensionRec {j} {C : Type j} (n s : C) (p : A → n == s)
  = PushoutRec {d = suspension-span} (λ _ → n) (λ _ → s) p

module SuspensionRecType {j} (n s : Type j) (p : A → n ≃ s)
  = PushoutRecType {d = suspension-span} (λ _ → n) (λ _ → s) p
