{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cw.CW
open import cw.FinCW
open import cw.FinBoundary
open import cohomology.Theory

{- The reason that RephraseDualizedFirstFinBoundary did not handle this case
   is because [FinSkeleton n] does not compute. -}

module cw.cohomology.cochainequiv.DualizedFirstBoundary (OT : OrdinaryTheory lzero)
  (⊙fin-skel : ⊙FinSkeleton 1) where

open OrdinaryTheory OT

private
  fin-skel = ⊙FinSkeleton.skel ⊙fin-skel
  I = AttachedFinSkeleton.numCells fin-skel
  
  I₋₁ = AttachedFinSkeleton.skel fin-skel

abstract
  rephrase-dualized-first-boundary-in-degree : ∀ g <I
    →  FormalSum-extend (C2-abgroup 0) g (GroupHom.f (fboundary-last fin-skel) fs[ inl <I :: nil ])
    == Group.sum (C2 0) (λ <I₋₁ → Group.exp (C2 0) (g <I₋₁) (fdegree-last fin-skel <I <I₋₁))
  rephrase-dualized-first-boundary-in-degree g <I =
    FormalSum-extend (C2-abgroup 0) g (GroupHom.f (fboundary-last fin-skel) fs[ inl <I :: nil ])
      =⟨ ap (FormalSum-extend (C2-abgroup 0) g) $
          app= (is-equiv.g-f (FreeAbGroup-extend-is-equiv (FreeAbGroup (Fin I₋₁))) (fboundary'-last fin-skel)) <I ⟩
    FormalSum-extend (C2-abgroup 0) g
      (Group.sum (FreeAbGroup.grp (Fin I₋₁))
        (λ <I₋₁ → Group.exp (FreeAbGroup.grp (Fin I₋₁)) fs[ inl <I₋₁ :: nil ] (fdegree-last fin-skel <I <I₋₁)))
      =⟨ GroupHom.pres-sum (FreeAbGroup-extend (C2-abgroup 0) g)
          (λ <I₋₁ → Group.exp (FreeAbGroup.grp (Fin I₋₁)) fs[ inl <I₋₁ :: nil ] (fdegree-last fin-skel <I <I₋₁)) ⟩
    Group.sum (C2 0)
      (λ <I₋₁ → 
        (FormalSum-extend (C2-abgroup 0) g
          (Group.exp (FreeAbGroup.grp (Fin I₋₁)) fs[ inl <I₋₁ :: nil ] (fdegree-last fin-skel <I <I₋₁))))
      =⟨ ap (Group.sum (C2 0))
          (λ= λ <I₋₁ →
            GroupHom.pres-exp (FreeAbGroup-extend (C2-abgroup 0) g)
              fs[ inl <I₋₁ :: nil ]
              (fdegree-last fin-skel <I <I₋₁)) ⟩
    Group.sum (C2 0)
      (λ <I₋₁ → 
        (Group.exp (C2 0)
          (FormalSum-extend (C2-abgroup 0) g fs[ inl <I₋₁ :: nil ])
          (fdegree-last fin-skel <I <I₋₁)))
      =⟨ ap (Group.sum (C2 0))
          (λ= λ <I₋₁ → ap (λ g → Group.exp (C2 0) g (fdegree-last fin-skel <I <I₋₁)) $
            app= (is-equiv.g-f (FreeAbGroup-extend-is-equiv (C2-abgroup 0)) g) <I₋₁) ⟩
    Group.sum (C2 0) (λ <I₋₁ → (Group.exp (C2 0) (g <I₋₁) (fdegree-last fin-skel <I <I₋₁)))
      =∎
