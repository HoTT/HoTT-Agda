{-# OPTIONS --without-K #-}

open import HoTT

module cw.Attach {i j} where

Boundry : (A : Type i) (B : Type j) (n : ℕ) (k : ULevel) → Type (lmax i (lmax j k))
Boundry A B n k = A → Sphere {k} n → B

module _ {k : ULevel} {A : Type i} {B : Type j} (n : ℕ) where

  Attach-span : Boundry A B n k → Span {i} {j} {lmax i k}
  Attach-span boundary = span A B (A × Sphere n) fst (uncurry boundary)

  Attach : Boundry A B n k → Type (lmax i (lmax j k))
  Attach boundary = Pushout (Attach-span boundary)

module _ {k : ULevel} {A : Type i} {B : Type j} {n : ℕ} {boundary : Boundry A B n k} where

  -- Inspired by mountains

  ground : B → Attach n boundary
  ground b = right b

  peak : A → Attach n boundary
  peak a = left a

  attach : (a : A) (s : Sphere {k} n) → peak a == ground (boundary a s)
  attach a s = glue (a , s)

  module AttachElim {l} {P : Attach n boundary → Type l}
    (ground* : (b : B) → P (ground b))
    (peak* : (a : A) → P (peak a))
    (attach* : (a : A) (s : Sphere {k} n)
      → peak* a == ground* (boundary a s) [ P ↓ attach a s ]) where

    module P = PushoutElim
      {d = Attach-span n boundary} {P = P}
      peak* ground* (uncurry attach*)

    f = P.f
    attach-β = curry P.glue-β

  open AttachElim public using () renaming (f to Attach-elim)

  module AttachRec {l} {D : Type l}
    (ground* : (b : B) → D)
    (peak* : (a : A) → D)
    (attach* : (a : A) (s : Sphere {k} n) → peak* a == ground* (boundary a s)) where

    module P = PushoutRec
      {d = Attach-span n boundary} {D = D}
      peak* ground* (uncurry attach*)

    f = P.f
    attach-β = curry P.glue-β

  open AttachRec public using () renaming (f to Attach-rec)

