{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Span
open import lib.types.Pushout
open import lib.types.PushoutFlattening
open import lib.types.Unit
open import lib.types.Pointed

-- Wedge of two pointed types is defined as a particular case of pushout

module lib.types.Wedge where

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  wedge-span : Span
  wedge-span = span (fst X) (fst Y) Unit (λ _ → snd X) (λ _ → snd Y)

  Wedge : Type (lmax i j)
  Wedge = Pushout wedge-span

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  winl : fst X → Wedge X Y
  winl x = left x

  winr : fst Y → Wedge X Y
  winr y = right y

  wglue : winl (snd X) == winr (snd Y)
  wglue = glue tt

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  Ptd-Wedge : Ptd (lmax i j)
  Ptd-Wedge = ∙[ Wedge X Y , winl (snd X) ]

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  ptd-winl : fst (X ∙→ Ptd-Wedge X Y)
  ptd-winl = (winl , idp)

  ptd-winr : fst (Y ∙→ Ptd-Wedge X Y)
  ptd-winr = (winr , ! wglue)

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  module WedgeElim {k} {P : Wedge X Y → Type k}
    (f : (x : fst X) → P (winl x)) (g : (y : fst Y) → P (winr y))
    (p : f (snd X) == g (snd Y) [ P ↓ wglue ])
    = PushoutElim f g (λ _ → p)

  open WedgeElim public using () renaming (f to Wedge-elim)

  module WedgeRec {k} {C : Type k} (f : fst X → C) (g : fst Y → C)
    (p : f (snd X) == g (snd Y))
    = PushoutRec {d = wedge-span X Y} f g (λ _ → p)

  module WedgeRecType {k} (f : fst X → Type k) (g : fst Y → Type k)
    (p : f (snd X) ≃ g (snd Y))
    = PushoutRecType {d = wedge-span X Y} f g (λ _ → p)
