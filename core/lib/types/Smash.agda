{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Bool
open import lib.types.Coproduct
open import lib.types.Paths
open import lib.types.Span
open import lib.types.Pushout
open import lib.types.Cofiber
open import lib.types.Sigma
open import lib.types.Wedge

module lib.types.Smash {i j} where

module _ (X : Ptd i) (Y : Ptd j) where

  ⊙∧-span : ⊙Span
  ⊙∧-span = ⊙span ⊙Bool (X ⊙× Y) (X ⊙⊔ Y)
    (⊙⊔-fmap {Y = Y} ⊙cst ⊙cst)
    (⊔-rec (_, pt Y) (pt X ,_) , idp)

  ∧-span : Span
  ∧-span = ⊙Span-to-Span ⊙∧-span

  _∧_ = Pushout ∧-span
  _⊙∧_ = ⊙Pushout ⊙∧-span
  Smash = _∧_
  ⊙Smash = _⊙∧_

module _ {X : Ptd i} {Y : Ptd j} where

  smbasel : Smash X Y
  smbasel = left true

  smbaser : Smash X Y
  smbaser = left false

  smin : de⊙ X → de⊙ Y → Smash X Y
  smin x y = right (x , y)

  smgluel : (x : de⊙ X) → smbasel == smin x (pt Y)
  smgluel x = glue (inl x)

  smgluer : (y : de⊙ Y) → smbaser == smin (pt X) y
  smgluer y = glue (inr y)

  module SmashElim {k} {P : Smash X Y → Type k}
    (smbasel* : P smbasel) (smbaser* : P smbaser)
    (smin* : (x : de⊙ X) (y : de⊙ Y) → P (right (x , y)))
    (smgluel* : (x : de⊙ X) → smbasel* == smin* x (pt Y) [ P ↓ smgluel x ])
    (smgluer* : (y : de⊙ Y) → smbaser* == smin* (pt X) y [ P ↓ smgluer y ]) where

    private
      module M = PushoutElim
        (Coprod-elim (λ _ → smbasel*) (λ _ → smbaser*))
        (uncurry smin*)
        (Coprod-elim smgluel* smgluer*)
    f = M.f
    smgluel-β = M.glue-β ∘ inl
    smgluer-β = M.glue-β ∘ inr

  Smash-elim = SmashElim.f

  module SmashRec {k} {C : Type k}
    (smbasel* smbaser* : C)
    (smin* : (x : de⊙ X) (y : de⊙ Y) → C)
    (smgluel* : (x : de⊙ X) → smbasel* == smin* x (pt Y))
    (smgluer* : (y : de⊙ Y) → smbaser* == smin* (pt X) y) where

    private
      module M = PushoutRec {d = ∧-span X Y}
        (Coprod-rec (λ _ → smbasel*) (λ _ → smbaser*))
        (uncurry smin*)
        (Coprod-elim smgluel* smgluer*)
    f = M.f
    smgluel-β = M.glue-β ∘ inl
    smgluer-β = M.glue-β ∘ inr

  Smash-rec = SmashRec.f
