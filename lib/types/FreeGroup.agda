{-# OPTIONS --without-K #-}

open import lib.Basics

module lib.types.FreeGroup where

module _ {i} where

  private
    data #FreeGroup-aux (A : Type i) : Type i where
      #fg-nil : #FreeGroup-aux A
      _#fg::_ : A → #FreeGroup-aux A → #FreeGroup-aux A
      _#fg-inv::_ : A → #FreeGroup-aux A → #FreeGroup-aux A

    {- Is this okay?  The template is to have 'data' here,
     - but then the β rules for paths will not typecheck.
     -}
    record #FreeGroup (A : Type i) : Type i where
      constructor
        #freegroup
      field
        #freegroup-proj : #FreeGroup-aux A
        #freegroup-unit : Unit → Unit

  FreeGroup : (A : Type i) → Type i
  FreeGroup A = #FreeGroup A

  module _ {A : Type i} where

    fg-nil : FreeGroup A
    fg-nil = #freegroup #fg-nil _

    infixr 60 _fg::_
    _fg::_ : A → FreeGroup A → FreeGroup A
    a fg:: (#freegroup fg _) = #freegroup (a #fg:: fg) _
    
    infixr 60 _fg-inv::_
    _fg-inv::_ : A → FreeGroup A → FreeGroup A
    a fg-inv:: (#freegroup fg _) = #freegroup (a #fg-inv:: fg) _

    postulate  -- HIT
      fg-inv-l : ∀ (a : A) → (fg : FreeGroup A) → a fg-inv:: a     fg:: fg == fg
      fg-inv-r : ∀ (a : A) → (fg : FreeGroup A) → a fg::     a fg-inv:: fg == fg

    postulate  -- HIT
      FreeGroup-level : is-set (FreeGroup A)

    FreeGroup-is-set = FreeGroup-level

    module FreeGroupElim {j} {P : FreeGroup A → Type j}
      (p : (x : FreeGroup A) → is-set (P x)) (nil* : P fg-nil)
      (_fg::*_ : ∀ a {fg} (fg* : P fg) → P (a fg:: fg))
      (_fg-inv::*_ : ∀ a {fg} (fg* : P fg) → P (a fg-inv:: fg))
      (fg-inv-l* : ∀ a {fg} (fg* : P fg) → (a fg-inv::* (a     fg::* fg*)) == fg* [ P ↓ fg-inv-l a fg ] )
      (fg-inv-r* : ∀ a {fg} (fg* : P fg) → (a fg::*     (a fg-inv::* fg*)) == fg* [ P ↓ fg-inv-r a fg ]) where


      f : Π (FreeGroup A) P
      f = f-aux phantom phantom phantom where

        f-aux* : Π (#FreeGroup-aux A) (P ∘ (λ fg → #freegroup fg _))
        f-aux* #fg-nil = nil*
        f-aux* (a #fg:: fg) = a fg::* f-aux* fg
        f-aux* (a #fg-inv:: fg) = a fg-inv::* f-aux* fg

        f-aux : Phantom p → Phantom fg-inv-l* → Phantom fg-inv-r*
          → Π (FreeGroup A) P
        f-aux phantom phantom phantom (#freegroup fg _) = f-aux* fg

      postulate  -- HIT
        fg-inv-l-β : ∀ a fg → apd f (fg-inv-l a fg) == fg-inv-l* a (f fg)
        fg-inv-r-β : ∀ a fg → apd f (fg-inv-r a fg) == fg-inv-r* a (f fg)

open FreeGroupElim public renaming (f to FreeGroup-elim)

module FreeGroupRec {i} {A : Type i} {j} {B : Type j} (p : is-set B)
  (nil* : B) (_fg::*[_]_ : A → FreeGroup A → B → B) (_fg-inv::*[_]_ : A → FreeGroup A → B → B)
  (fg-inv-l* : ∀ a {fg} fg* → (a fg-inv::*[ a     fg:: fg ] (a     fg::*[ fg ] fg*)) == fg*)
  (fg-inv-r* : ∀ a {fg} fg* → (a     fg::*[ a fg-inv:: fg ] (a fg-inv::*[ fg ] fg*)) == fg*) where

  private
    module M = FreeGroupElim (λ x → p) nil*
      (λ a {fg} fg* → a     fg::*[ fg ] fg*)
      (λ a {fg} fg* → a fg-inv::*[ fg ] fg*)
      (λ a {fg} fg* → ↓-cst-in (fg-inv-l* a {fg} fg*))
      (λ a {fg} fg* → ↓-cst-in (fg-inv-r* a {fg} fg*))

  f : FreeGroup A → B
  f = M.f

open FreeGroupRec public renaming (f to FreeGroup-rec)
