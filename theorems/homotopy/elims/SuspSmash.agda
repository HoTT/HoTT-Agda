{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.elims.Lemmas
open import homotopy.elims.CofPushoutSection

module homotopy.elims.SuspSmash {i j k} {X : Ptd i} {Y : Ptd j}
  {P : Susp (X ∧ Y) → Type k}
  (north* : P north) (south* : P south)
  (cod* : (s : fst X × fst Y) → north* == south* [ P ↓ merid (cfcod s) ])
  where

private
  base* = transport (λ κ → north* == south* [ P ↓ merid κ ])
    (! (cfglue (winl (snd X))))
    (cod* (snd X , snd Y))

  coh* : (s : X ∧ Y) → north* == south* [ P ↓ merid s ]
  coh* = CofPushoutSection.elim (λ _ → tt) (λ _ → idp)
    base*
    (λ {(x , y) →
      (fst (fillX x) ∙ fst (fillY y)) ◃ fst fill0 ◃ cod* (x , y)})
    (↓↓-from-squareover ∘ λ x →
      snd (fillX x) ↓⊡h∙
      ap (λ p → p ◃ fst fill0 ◃ cod* (x , snd Y))
         (! (ap (λ q → fst (fillX x) ∙ q) fillY-lemma ∙ ∙-unit-r _)))
    (↓↓-from-squareover ∘ λ y →
      snd (fillY y) ↓⊡h∙
      ap (λ p → p ◃ fst fill0 ◃ cod* (snd X , y))
         (! (ap (λ q → q ∙ fst (fillY y)) fillX-lemma)))
    where
    fill-lemma : (w : X ∨ Y)
      (α : north* == south* [ P ↓ merid (cfcod (∨-in-× X Y w)) ])
      → Σ (north* == north*)
          (λ p → SquareOver P (natural-square merid (cfglue w))
                   base*
                   (↓-ap-in _ _ (apd (λ _ → north*) (cfglue w)))
                   (↓-ap-in _ _ (apd (λ _ → south*) (cfglue w)))
                   (p ◃ α))
    fill-lemma w α = fill-upper-right _ _ _ _ _

    fill0 = fill-lemma (winl (snd X)) (cod* (snd X , snd Y))
    fillX = λ x → fill-lemma (winl x) (fst fill0 ◃ cod* (x , snd Y))
    fillY = λ y → fill-lemma (winr y) (fst fill0 ◃ cod* (snd X , y))

    fillX-lemma : fst (fillX (snd X)) == idp
    fillX-lemma = ! $
      fill-upper-right-unique _ _ _ _ _ idp (snd fill0 ↓⊡h∙ ! (idp◃ _))

    fillY-lemma : fst (fillY (snd Y)) == idp
    fillY-lemma = ! $
      fill-upper-right-unique _ _ _ _ _ idp (snd fill0 ↓⊡h∙ ! (idp◃ _))
      ∙ ap (λ w → fst (fill-lemma w (fst fill0 ◃ cod* (∨-in-× X Y w))))
           wglue

susp-smash-elim : Π (Susp (X ∧ Y)) P
susp-smash-elim = Susp-elim north* south* coh*
