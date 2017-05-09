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
  ⊙∧-span = ⊙span (X ⊙× Y) ⊙Bool (X ⊙⊔ Y)
    (⊔-rec (_, pt Y) (pt X ,_) , idp)
    (⊙⊔-fmap {Y = Y} ⊙cst ⊙cst)

  ∧-span : Span
  ∧-span = ⊙Span-to-Span ⊙∧-span

  _∧_ = Pushout ∧-span
  _⊙∧_ = ⊙Pushout ⊙∧-span
  Smash = _∧_
  ⊙Smash = _⊙∧_

module _ {X : Ptd i} {Y : Ptd j} where

  smin : de⊙ X → de⊙ Y → Smash X Y
  smin x y = left (x , y)

  smbasel : Smash X Y
  smbasel = right true

  smbaser : Smash X Y
  smbaser = right false

  smgluel : (x : de⊙ X) → smin x (pt Y) == smbasel
  smgluel x = glue (inl x)

  smgluer : (y : de⊙ Y) → smin (pt X) y == smbaser
  smgluer y = glue (inr y)

  module SmashElim {k} {P : Smash X Y → Type k}
    (smin* : (x : de⊙ X) (y : de⊙ Y) → P (smin x y))
    (smbasel* : P smbasel) (smbaser* : P smbaser)
    (smgluel* : (x : de⊙ X) → smin* x (pt Y) == smbasel* [ P ↓ smgluel x ])
    (smgluer* : (y : de⊙ Y) → smin* (pt X) y == smbaser* [ P ↓ smgluer y ]) where

    private
      module M = PushoutElim
        (uncurry smin*)
        (Coprod-elim (λ _ → smbasel*) (λ _ → smbaser*))
        (Coprod-elim smgluel* smgluer*)
    f = M.f
    smgluel-β = M.glue-β ∘ inl
    smgluer-β = M.glue-β ∘ inr

  Smash-elim = SmashElim.f

  module SmashRec {k} {C : Type k}
    (smin* : (x : de⊙ X) (y : de⊙ Y) → C)
    (smbasel* smbaser* : C)
    (smgluel* : (x : de⊙ X) → smin* x (pt Y) == smbasel*)
    (smgluer* : (y : de⊙ Y) → smin* (pt X) y == smbaser*) where

    private
      module M = PushoutRec {d = ∧-span X Y}
        (uncurry smin*)
        (Coprod-rec (λ _ → smbasel*) (λ _ → smbaser*))
        (Coprod-elim smgluel* smgluer*)
    f = M.f
    smgluel-β = M.glue-β ∘ inl
    smgluer-β = M.glue-β ∘ inr

  Smash-rec = SmashRec.f
