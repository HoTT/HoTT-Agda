{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.elims.Lemmas

module homotopy.elims.SuspSmash {i j k} {X : Ptd i} {Y : Ptd j}
  {P : Susp (X ∧ Y) → Type k}
  (north* : P north) (south* : P south)
  (smin* : (x : de⊙ X) (y : de⊙ Y) → north* == south* [ P ↓ merid (smin x y) ])
  where

private
  smbase*-template : ∀ {s} (p : s == smin (pt X) (pt Y))
    → north* == south* [ P ↓ merid s ]
  smbase*-template p = transport! (λ κ → north* == south* [ P ↓ merid κ ])
    p (smin* (pt X) (pt Y))

  smbasel* = smbase*-template (smgluel (pt X))
  smbaser* = smbase*-template (smgluer (pt Y))

  -- note that [smin*] is adjusted.
  coh* : (s : X ∧ Y) → north* == south* [ P ↓ merid s ]
  coh* = Smash-elim smbasel* smbaser*
    (λ x y → fst (fill-l x) ◃ fst (fill-r y) ◃ fst fill-base ◃ smin* x y)
    (λ x → ↓↓-from-squareover $
      snd (fill-l x) ↓⊡h∙ ap (fst (fill-l x) ◃_) (! (idp◃ _)) ↓⊡h∙
      ap (λ p → fst (fill-l x) ◃ p ◃ fst fill-base ◃ smin* x (pt Y)) (! fill-r-β))
    (λ y → ↓↓-from-squareover $
      snd (fill-r y) ↓⊡h∙ ! (idp◃ _) ↓⊡h∙
      ap (λ p → p ◃ fst (fill-r y) ◃ fst fill-base ◃ smin* (pt X) y) (! fill-l-β))
    where
    fill-template : ∀ {s₁ s₂} (p : s₁ == s₂)
      (α : north* == south* [ P ↓ merid s₁ ])
      (β : north* == south* [ P ↓ merid s₂ ])
      → Σ (north* == north*)
          (λ q → SquareOver P (natural-square merid p)
                   α
                   (↓-ap-in _ _ (apd (λ _ → north*) p))
                   (↓-ap-in _ _ (apd (λ _ → south*) p))
                   (q ◃ β))
    fill-template p α β = fill-upper-right _ _ _ _ _

    fill-base = fill-template (smgluel (pt X)) smbasel* (smin* (pt X) (pt Y))
    fill-l = λ x → fill-template (smgluel x) smbasel* (fst fill-base ◃ smin* x (pt Y))
    fill-l-β : fst (fill-l (pt X)) == idp
    fill-l-β = ! $
      fill-upper-right-unique _ _ _ _ _ idp (snd fill-base ↓⊡h∙ ! (idp◃ _))

    fill-r = λ y → fill-template (smgluer y) smbaser* (fst fill-base ◃ smin* (pt X) y)
    fill-r-β : fst (fill-r (pt Y)) == idp
    fill-r-β = ! $
      fill-upper-right-unique _ _ _ _ _ idp (snd fill-base ↓⊡h∙ ! (idp◃ _))
      ∙ ap (λ sp → fst (fill-template (snd sp) (smbase*-template (snd sp))
                                      (fst fill-base ◃ smin* (pt X) (pt Y))))
           (contr-has-all-paths (pathto-is-contr (smin (pt X) (pt Y)))
                                (smbasel , smgluel (pt X))
                                (smbaser , smgluer (pt Y)))

SuspSmash-elim : Π (Susp (X ∧ Y)) P
SuspSmash-elim = Susp-elim north* south* coh*
