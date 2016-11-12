{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Coproduct
open import lib.types.Paths
open import lib.types.Pointed
open import lib.types.Pushout
open import lib.types.PushoutFlattening
open import lib.types.PushoutFmap
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

  ⊙winl : X ⊙→ X ⊙∨ Y
  ⊙winl = (winl , idp)

  ⊙winr : Y ⊙→ X ⊙∨ Y
  ⊙winr = (winr , ! wglue)

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  module WedgeElim {k} {P : X ∨ Y → Type k}
    (inl* : (x : fst X) → P (winl x)) (inr* : (y : fst Y) → P (winr y))
    (glue* : inl* (snd X) == inr* (snd Y) [ P ↓ wglue ]) where

    private
      module M = PushoutElim inl* inr* (λ _ → glue*)

    f = M.f
    glue-β = M.glue-β unit

  open WedgeElim public using () renaming (f to Wedge-elim)

  module WedgeRec {k} {C : Type k} (inl* : fst X → C) (inr* : fst Y → C)
    (glue* : inl* (snd X) == inr* (snd Y)) where

    private
      module M = PushoutRec {d = wedge-span X Y} inl* inr* (λ _ → glue*)

    f = M.f
    glue-β = M.glue-β unit

  open WedgeRec public using () renaming (f to Wedge-rec)

module ⊙WedgeRec {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (g : X ⊙→ Z) (h : Y ⊙→ Z) where

  open WedgeRec (fst g) (fst h) (snd g ∙ ! (snd h)) public

  ⊙f : X ⊙∨ Y ⊙→ Z
  ⊙f = (f , snd g)

  ⊙winl-β : ⊙f ⊙∘ ⊙winl == g
  ⊙winl-β = idp

  ⊙winr-β : ⊙f ⊙∘ ⊙winr == h
  ⊙winr-β = ⊙λ= (λ _ → idp) $
    ap (_∙ snd g)
       (ap-! f wglue ∙ ap ! glue-β ∙ !-∙ (snd g) (! (snd h)))
    ∙ ∙-assoc (! (! (snd h))) (! (snd g)) (snd g)
    ∙ ap (! (! (snd h)) ∙_) (!-inv-l (snd g))
    ∙ ∙-unit-r (! (! (snd h)))
    ∙ !-! (snd h)

⊙Wedge-rec = ⊙WedgeRec.⊙f

⊙Wedge-rec-post∘ : ∀ {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (k : Z ⊙→ W) (g : X ⊙→ Z) (h : Y ⊙→ Z)
  → k ⊙∘ ⊙Wedge-rec g h == ⊙Wedge-rec (k ⊙∘ g) (k ⊙∘ h)
⊙Wedge-rec-post∘ k g h = ⊙λ=
  (Wedge-elim (λ _ → idp) (λ _ → idp)
    (↓-='-in' $ ⊙WedgeRec.glue-β (k ⊙∘ g) (k ⊙∘ h)
               ∙ lemma (fst k) (snd g) (snd h) (snd k)
               ∙ ! (ap (ap (fst k)) (⊙WedgeRec.glue-β g h))
               ∙ ∘-ap (fst k) (fst (⊙Wedge-rec g h)) wglue))
  idp
  where
  lemma : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y z : A} {w : B}
    (p : x == z) (q : y == z) (r : f z == w)
    → (ap f p ∙ r) ∙ ! (ap f q ∙ r) == ap f (p ∙ ! q)
  lemma f idp idp idp = idp

⊙Wedge-rec-η : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  → ⊙Wedge-rec ⊙winl ⊙winr == ⊙idf (X ⊙∨ Y)
⊙Wedge-rec-η = ⊙λ=
  (Wedge-elim (λ _ → idp) (λ _ → idp)
    (↓-='-in' $ ap-idf wglue
               ∙ ! (!-! wglue)
               ∙ ! (⊙WedgeRec.glue-β ⊙winl ⊙winr)))
  idp

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  add-wglue : fst (X ⊙⊔ Y) → X ∨ Y
  add-wglue (inl x) = winl x
  add-wglue (inr y) = winr y

  ⊙add-wglue : X ⊙⊔ Y ⊙→ X ⊙∨ Y
  ⊙add-wglue = add-wglue , idp

module Fold {i} {X : Ptd i} = ⊙WedgeRec (⊙idf X) (⊙idf X)
fold = Fold.f
⊙fold = Fold.⊙f

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  module Projl = ⊙WedgeRec (⊙idf X) (⊙cst {X = Y})
  module Projr = ⊙WedgeRec (⊙cst {X = X}) (⊙idf Y)

  projl = Projl.f
  projr = Projr.f
  ⊙projl = Projl.⊙f
  ⊙projr = Projr.⊙f

module _ {i i' j j'} {X : Ptd i} {X' : Ptd i'} {Y : Ptd j} {Y' : Ptd j'}
  (eqX : X ⊙≃ X') (eqY : Y ⊙≃ Y') where

  wedge-span-emap : SpanEquiv (wedge-span X Y) (wedge-span X' Y')
  wedge-span-emap = ( span-map (fst (fst eqX)) (fst (fst eqY)) (idf _)
                        (comm-sqr λ _ → snd (fst eqX))
                        (comm-sqr λ _ → snd (fst eqY))
                    , snd eqX , snd eqY , idf-is-equiv _)

  ∨-emap : X ∨ Y ≃ X' ∨ Y'
  ∨-emap = Pushout-emap wedge-span-emap

  ⊙∨-emap : X ⊙∨ Y ⊙≃ X' ⊙∨ Y'
  ⊙∨-emap = ≃-to-⊙≃ ∨-emap (ap winl (snd (fst eqX)))
