{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Coproduct
open import lib.types.Pointed
open import lib.types.Pushout
open import lib.types.PushoutFlattening
open import lib.types.Span
open import lib.types.Unit

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
    (winl* : (x : fst X) → P (winl x)) (winr* : (y : fst Y) → P (winr y))
    (wglue* : winl* (snd X) == winr* (snd Y) [ P ↓ wglue ]) where

    private
      module M = PushoutElim winl* winr* (λ _ → wglue*)

    f = M.f
    glue-β = M.glue-β unit

  open WedgeElim public using () renaming (f to Wedge-elim)


  module WedgeRec {k} {C : Type k} (winl* : fst X → C) (winr* : fst Y → C)
    (wglue* : winl* (snd X) == winr* (snd Y)) where

    private
      module M = PushoutRec {d = wedge-span X Y} winl* winr* (λ _ → wglue*)

    f = M.f
    glue-β = M.glue-β unit


add-wglue : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  → fst (X ∙⊔ Y) → Wedge X Y
add-wglue (inl x) = winl x
add-wglue (inr y) = winr y

ptd-add-wglue : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  → fst (X ∙⊔ Y ∙→ Ptd-Wedge X Y)
ptd-add-wglue = (add-wglue , idp)


module Fold {i} {X : Ptd i} =
  WedgeRec {X = X} {Y = X} (λ x → x) (λ x → x) idp

fold = Fold.f

ptd-fold : ∀ {i} {X : Ptd i} → fst (Ptd-Wedge X X ∙→ X)
ptd-fold = (fold , idp)
