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

  cfbase' : Cofiber
  cfbase' = left tt

  cfcod' : B → Cofiber
  cfcod' b = right b

  cfglue' : (a : A) → cfbase' == cfcod' (f a)
  cfglue' a = glue a

module _ {i j} {A : Type i} {B : Type j} {f : A → B} where

  cfbase : Cofiber f
  cfbase = cfbase' f

  cfcod : B → Cofiber f
  cfcod = cfcod' f

  cfglue : (a : A) → cfbase == cfcod (f a)
  cfglue = cfglue' f

  module CofiberElim {k} {P : Cofiber f → Type k}
    (b : P cfbase) (c : (y : B) → P (cfcod y)) 
    (p : (x : A) → b == c (f x) [ P ↓ cfglue x ])
    = PushoutElim (λ _ → b) c p

  open CofiberElim public using () renaming (f to Cofiber-elim)

  module CofiberRec {k} {C : Type k} (b : C) (c : B → C)
    (p : (x : A) → b == c (f x))
    = PushoutRec {d = cofiber-span f} (λ _ → b) c p

  module CofiberRecType {k} (b : Type k) (c : B → Type k)
    (p : (x : A) → b ≃ c (f x))
    = PushoutRecType {d = cofiber-span f} (λ _ → b) c p

module _ {i j} {X : Ptd i} {Y : Ptd j} (F : fst (X ⊙→ Y)) where

  ⊙cof-span : ⊙Span
  ⊙cof-span = ⊙span ⊙Unit Y X ((λ _ → tt) , idp) F

  ⊙Cof : Ptd (lmax i j)
  ⊙Cof = ⊙Pushout ⊙cof-span

  ⊙cfcod' : fst (Y ⊙→ ⊙Cof)
  ⊙cfcod' = cfcod , ap cfcod (! (snd F)) ∙ ! (cfglue (snd X))

  ⊙cfglue' : ⊙cst == ⊙cfcod' ⊙∘ F
  ⊙cfglue' = ⊙λ= cfglue (lemma cfcod (cfglue (snd X)) (snd F))
    where
    lemma : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
      {x y : A} {z : B} (p : z == f x) (q : x == y)
      → idp == p ∙ ap f q ∙ ap f (! q) ∙ ! p
    lemma f idp idp = idp

module _ {i j} {X : Ptd i} {Y : Ptd j} {F : fst (X ⊙→ Y)} where

  ⊙cfcod : fst (Y ⊙→ ⊙Cof F)
  ⊙cfcod = ⊙cfcod' F

  ⊙cfglue : ⊙cst == ⊙cfcod ⊙∘ F
  ⊙cfglue = ⊙cfglue' F
