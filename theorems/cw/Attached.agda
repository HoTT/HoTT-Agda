{-# OPTIONS --without-K #-}

open import HoTT

module cw.Attached {i j k : ULevel} where

-- The type of attaching maps.
-- In intended uses, [B] is the type of cells and [C] is the [Sphere]s.
Attaching : (A : Type i) (B : Type j) (C : Type k) → Type (lmax i (lmax j k))
Attaching A B C = B → C → A

module _ {A : Type i} {B : Type j} {C : Type k} where

  -- [Attached] is the type with all the cells attached.

  attached-span : Attaching A B C → Span {i} {j} {lmax j k}
  attached-span attaching = span A B (B × C) (uncurry attaching) fst

  Attached : Attaching A B C → Type (lmax i (lmax j k))
  Attached attaching = Pushout (attached-span attaching)

module _ {A : Type i} {B : Type j} {C : Type k} {attaching : Attaching A B C} where

  incl : A → Attached attaching
  incl = left

  hub : B → Attached attaching
  hub = right

  spoke : ∀ b c → incl (attaching b c) == hub b
  spoke = curry glue

  module AttachedElim {l} {P : Attached attaching → Type l}
    (incl* : (a : A) → P (incl a))
    (hub* : (b : B) → P (hub b))
    (spoke* : (b : B) (c : C)
      → incl* (attaching b c) == hub* b [ P ↓ spoke b c ]) where

    module P = PushoutElim
      {d = attached-span attaching} {P = P}
      incl* hub* (uncurry spoke*)

    f = P.f
    spoke-β = curry P.glue-β

  open AttachedElim public using () renaming (f to Attached-elim)

  module AttachedRec {l} {D : Type l}
    (incl* : (a : A) → D)
    (hub* : (b : B) → D)
    (spoke* : (b : B) (c : C) → incl* (attaching b c) == hub* b) where

    module P = PushoutRec
      {d = attached-span attaching} {D = D}
      incl* hub* (uncurry spoke*)

    f = P.f
    spoke-β = curry P.glue-β

  open AttachedRec public using () renaming (f to Attached-rec)

