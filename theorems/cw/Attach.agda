{-# OPTIONS --without-K #-}

open import HoTT

module cw.Attach {i j k : ULevel} where

Boundry : (A : Type i) (B : Type j) (C : Type k) → Type (lmax i (lmax j k))
Boundry A B C = B → C → A

module _ {A : Type i} {B : Type j} {C : Type k} where

  Attach-span : Boundry A B C → Span {i} {j} {lmax j k}
  Attach-span boundary = span A B (B × C) (uncurry boundary) fst

  Attach : Boundry A B C → Type (lmax i (lmax j k))
  Attach boundary = Pushout (Attach-span boundary)

module _ {A : Type i} {B : Type j} {C : Type k} {boundary : Boundry A B C} where

  incl : A → Attach boundary
  incl = left

  hub : B → Attach boundary
  hub = right

  spoke : ∀ b c → incl (boundary b c) == hub b
  spoke = curry glue

  module AttachElim {l} {P : Attach boundary → Type l}
    (incl* : (a : A) → P (incl a))
    (hub* : (b : B) → P (hub b))
    (spoke* : (b : B) (c : C)
      → incl* (boundary b c) == hub* b [ P ↓ spoke b c ]) where

    module P = PushoutElim
      {d = Attach-span boundary} {P = P}
      incl* hub* (uncurry spoke*)

    f = P.f
    spoke-β = curry P.glue-β

  open AttachElim public using () renaming (f to Attach-elim)

  module AttachRec {l} {D : Type l}
    (incl* : (a : A) → D)
    (hub* : (b : B) → D)
    (spoke* : (b : B) (c : C) → incl* (boundary b c) == hub* b) where

    module P = PushoutRec
      {d = Attach-span boundary} {D = D}
      incl* hub* (uncurry spoke*)

    f = P.f
    spoke-β = curry P.glue-β

  open AttachRec public using () renaming (f to Attach-rec)

