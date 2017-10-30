{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.elims.Lemmas

module homotopy.elims.SuspSmash {i j k} {X : Ptd i} {Y : Ptd j}
  {P : Susp (X ∧ Y) → Type k}
  (north* : P north) (south* : P south)
  (smin* : (x : de⊙ X) (y : de⊙ Y) → north* == south* [ P ↓ merid (smin x y) ])
  where

private
  smbase*-template : ∀ {s} (p : smin (pt X) (pt Y) == s)
    → north* == south* [ P ↓ merid s ]
  smbase*-template p = transport (λ κ → north* == south* [ P ↓ merid κ ])
    p (smin* (pt X) (pt Y))

  smbasel* = smbase*-template (smgluel (pt X))
  smbaser* = smbase*-template (smgluer (pt Y))

  -- note that [smin*] is adjusted.
  coh* : (s : X ∧ Y) → north* == south* [ P ↓ merid s ]
  coh* = Smash-elim
    (λ x y → fst (fill-l x) ◃ fst (fill-r y) ◃ fst fill-base ◃ smin* x y)
    smbasel* smbaser*
    (λ x → ↓↓-from-squareover $
           ap (λ p → fst (fill-l x) ◃ p ◃ fst fill-base ◃ smin* x (pt Y)) fill-r-β
      ∙h↓⊡ ap (fst (fill-l x) ◃_) (idp◃ _)
      ∙h↓⊡ snd (fill-l x))
    (λ y → ↓↓-from-squareover $
           ap (λ p → p ◃ fst (fill-r y) ◃ fst fill-base ◃ smin* (pt X) y) fill-l-β
      ∙h↓⊡ idp◃ _
      ∙h↓⊡ snd (fill-r y))
    where
    fill-template : ∀ {s₁ s₂} (p : s₁ == s₂)
      (α : north* == south* [ P ↓ merid s₁ ])
      (β : north* == south* [ P ↓ merid s₂ ])
      → Σ (north* == north*)
          (λ q → SquareOver P (natural-square merid p)
                   (q ◃ α)
                   (↓-ap-in _ _ (apd (λ _ → north*) p))
                   (↓-ap-in _ _ (apd (λ _ → south*) p))
                   β)
    fill-template p α β = fill-upper-left _ _ _ _ _

    fill-base = fill-template (smgluel (pt X)) (smin* (pt X) (pt Y)) smbasel*
    fill-l = λ x → fill-template (smgluel x) (fst fill-base ◃ smin* x (pt Y)) smbasel*
    fill-l-β : fst (fill-l (pt X)) == idp
    fill-l-β = ! $
      fill-upper-left-unique _ _ _ _ _ idp (idp◃ _ ∙h↓⊡ snd fill-base)

    fill-r = λ y → fill-template (smgluer y) (fst fill-base ◃ smin* (pt X) y) smbaser*
    fill-r-β : fst (fill-r (pt Y)) == idp
    fill-r-β = ! $
      fill-upper-left-unique _ _ _ _ _ idp (idp◃ _ ∙h↓⊡ snd fill-base)
      ∙ ap (λ sp → fst (fill-template (snd sp)
                                      (fst fill-base ◃ smin* (pt X) (pt Y))
                                      (smbase*-template (snd sp))))
           (contr-has-all-paths {{pathfrom-is-contr (smin (pt X) (pt Y))}}
                                (smbasel , smgluel (pt X))
                                (smbaser , smgluer (pt Y)))

SuspSmash-elim : Π (Susp (X ∧ Y)) P
SuspSmash-elim = Susp-elim north* south* coh*
