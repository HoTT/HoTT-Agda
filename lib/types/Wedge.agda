{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Coproduct
open import lib.types.Paths
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

  infix 80 _∨_
  _∨_ = Wedge

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  winl : fst X → X ∨ Y
  winl x = left x

  winr : fst Y → X ∨ Y
  winr y = right y

  wglue : winl (snd X) == winr (snd Y)
  wglue = glue tt

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  ⊙Wedge : Ptd (lmax i j)
  ⊙Wedge = ⊙[ Wedge X Y , winl (snd X) ]

  infix 80 _⊙∨_
  _⊙∨_ = ⊙Wedge

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  ⊙winl : fst (X ⊙→ X ⊙∨ Y)
  ⊙winl = (winl , idp)

  ⊙winr : fst (Y ⊙→ X ⊙∨ Y)
  ⊙winr = (winr , ! wglue)

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  module WedgeElim {k} {P : X ∨ Y → Type k}
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
  → fst (X ⊙⊔ Y) → X ∨ Y
add-wglue (inl x) = winl x
add-wglue (inr y) = winr y

⊙add-wglue : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  → fst (X ⊙⊔ Y ⊙→ X ⊙∨ Y)
⊙add-wglue = (add-wglue , idp)

module ⊙WedgeRec {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (g : fst (X ⊙→ Z)) (h : fst (Y ⊙→ Z)) where

  open WedgeRec (fst g) (fst h) (snd g ∙ ! (snd h)) public

  ⊙f : fst (X ⊙∨ Y ⊙→ Z)
  ⊙f = (f , snd g)

  ⊙winl-β : ⊙f ⊙∘ ⊙winl == g
  ⊙winl-β = idp

  ⊙winr-β : ⊙f ⊙∘ ⊙winr == h
  ⊙winr-β = ⊙λ= (λ _ → idp) $
    ap (λ w → w ∙ snd g)
       (ap-! f wglue ∙ ap ! glue-β ∙ !-∙ (snd g) (! (snd h)))
    ∙ ∙-assoc (! (! (snd h))) (! (snd g)) (snd g)
    ∙ ap (λ w → ! (! (snd h)) ∙ w) (!-inv-l (snd g))
    ∙ ∙-unit-r (! (! (snd h)))
    ∙ !-! (snd h)

⊙wedge-rec = ⊙WedgeRec.⊙f

⊙wedge-rec-post∘ : ∀ {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (k : fst (Z ⊙→ W)) (g : fst (X ⊙→ Z)) (h : fst (Y ⊙→ Z))
  → k ⊙∘ ⊙wedge-rec g h == ⊙wedge-rec (k ⊙∘ g) (k ⊙∘ h)
⊙wedge-rec-post∘ k g h = ⊙λ=
  (Wedge-elim (λ _ → idp) (λ _ → idp)
    (↓-='-in $ ⊙WedgeRec.glue-β (k ⊙∘ g) (k ⊙∘ h)
               ∙ lemma (fst k) (snd g) (snd h) (snd k)
               ∙ ! (ap (ap (fst k)) (⊙WedgeRec.glue-β g h))
               ∙ ∘-ap (fst k) (fst (⊙wedge-rec g h)) wglue))
  idp
  where
  lemma : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y z : A} {w : B}
    (p : x == z) (q : y == z) (r : f z == w)
    → (ap f p ∙ r) ∙ ! (ap f q ∙ r) == ap f (p ∙ ! q)
  lemma f idp idp idp = idp

⊙wedge-rec-η : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  → ⊙wedge-rec ⊙winl ⊙winr == ⊙idf (X ⊙∨ Y)
⊙wedge-rec-η = ⊙λ=
  (Wedge-elim (λ _ → idp) (λ _ → idp)
    (↓-='-in $ ap-idf wglue
               ∙ ! (!-! wglue)
               ∙ ! (⊙WedgeRec.glue-β ⊙winl ⊙winr)))
  idp

module Fold {i} {X : Ptd i} = ⊙WedgeRec (⊙idf X) (⊙idf X)
fold = Fold.f
⊙fold = Fold.⊙f
