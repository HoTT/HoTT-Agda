{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Span
open import lib.types.Pushout
open import lib.types.PushoutFlattening
open import lib.types.Unit
open import lib.types.Pointed

-- Cofiber is defined as a particular case of pushout

module lib.types.Cofiber {i j} {A : Type i} {B : Type j} (f : A → B) where

cofiber-span : Span
cofiber-span = span Unit B A (λ _ → tt) f

Cofiber : Type (lmax i j)
Cofiber = Pushout cofiber-span

cfbase : Cofiber
cfbase = left tt

cfcod : B → Cofiber
cfcod b = right b

cfglue : (a : A) → cfbase == cfcod (f a)
cfglue a = glue a

Ptd-Cof : Ptd (lmax i j)
Ptd-Cof = ∙[ Cofiber , cfbase ]

module CofiberElim {k} {P : Cofiber → Type k}
  (b : P cfbase) (c : (y : B) → P (cfcod y)) 
  (p : (x : A) → b == c (f x) [ P ↓ cfglue x ])
  = PushoutElim (λ _ → b) c p

open CofiberElim public using () renaming (f to Cofiber-elim)

module CofiberRec {k} {C : Type k} (b : C) (c : B → C)
  (p : (x : A) → b == c (f x))
  = PushoutRec {d = cofiber-span} (λ _ → b) c p

module CofiberRecType {k} (b : Type k) (c : B → Type k)
  (p : (x : A) → b ≃ c (f x))
  = PushoutRecType {d = cofiber-span} (λ _ → b) c p
