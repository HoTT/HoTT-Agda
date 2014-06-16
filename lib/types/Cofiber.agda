{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Span
open import lib.types.Pushout
open import lib.types.PushoutFlattening
open import lib.types.Unit
open import lib.types.Pointed

-- Cofiber is defined as a particular case of pushout

module lib.types.Cofiber where

module _ {i j} {A : Type i} {B : Type j} (f : A → B) where

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

module _ {i j} {X : Ptd i} {Y : Ptd j} (F : fst (X ∙→ Y)) where

  ptd-cof-span : Ptd-Span
  ptd-cof-span = ptd-span Ptd-Unit Y X ((λ _ → tt) , idp) F

  Ptd-Cof : Ptd (lmax i j)
  Ptd-Cof = Ptd-Pushout ptd-cof-span

  ptd-cfcod : fst (Y ∙→ Ptd-Cof)
  ptd-cfcod = 
    cfcod (fst F) , ap (cfcod (fst F)) (! (snd F)) ∙ ! (cfglue (fst F) (snd X))
