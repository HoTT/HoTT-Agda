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
open FreeAbelianGroup

private
  fin-skel = ⊙FinSkeleton.skel ⊙fin-skel
  I = AttachedFinSkeleton.numCells fin-skel

  I₋₁ = AttachedFinSkeleton.skel fin-skel

  module FAG   = FreeAbelianGroup (Fin I)
  module FAG₋₁ = FreeAbelianGroup (Fin I₋₁)

  open FAG   renaming (FreeAbGroup to G)   using ()
  open FAG₋₁ renaming (FreeAbGroup to G₋₁) using ()

abstract
  rephrase-dualized-first-boundary-in-degree : ∀ g <I
    →  GroupHom.f (Freeness.extend _ (C2-abgroup 0) g) (GroupHom.f (fboundary-last fin-skel) (FAG.insert <I))
    == Group.sum (C2 0) (λ <I₋₁ → Group.exp (C2 0) (g <I₋₁) (fdegree-last fin-skel <I <I₋₁))
  rephrase-dualized-first-boundary-in-degree g <I =
    γ.f (GroupHom.f (fboundary-last fin-skel) (FAG.insert <I))
      =⟨ ap γ.f $ app= (is-equiv.g-f (FAG.Freeness.extend-is-equiv G₋₁) (fboundary'-last fin-skel)) <I ⟩
    γ.f (G₋₁.sum (λ <I₋₁ → G₋₁.exp (FAG₋₁.insert <I₋₁) (fdegree-last fin-skel <I <I₋₁)))
      =⟨ γ.pres-sum (λ <I₋₁ → G₋₁.exp (FAG₋₁.insert <I₋₁) (fdegree-last fin-skel <I <I₋₁)) ⟩
    C⁰2.sum (λ <I₋₁ → (γ.f (G₋₁.exp (FAG₋₁.insert <I₋₁) (fdegree-last fin-skel <I <I₋₁))))
      =⟨ ap C⁰2.sum (λ= λ <I₋₁ → γ.pres-exp (FAG₋₁.insert <I₋₁) (fdegree-last fin-skel <I <I₋₁)) ⟩
    C⁰2.sum (λ <I₋₁ → (C⁰2.exp (γ.f (FAG₋₁.insert <I₋₁)) (fdegree-last fin-skel <I <I₋₁)))
      =⟨ ap C⁰2.sum
          (λ= λ <I₋₁ → ap (λ g → C⁰2.exp g (fdegree-last fin-skel <I <I₋₁)) $
            app= (is-equiv.g-f (FAG₋₁.Freeness.extend-is-equiv C⁰2) g) <I₋₁) ⟩
    C⁰2.sum (λ <I₋₁ → (C⁰2.exp (g <I₋₁) (fdegree-last fin-skel <I <I₋₁)))
      =∎
    where
      C⁰2 : AbGroup lzero
      C⁰2 = C2-abgroup 0
      module C⁰2 = AbGroup C⁰2
      γ : G₋₁.grp →ᴳ C⁰2.grp
      γ = FAG₋₁.Freeness.extend C⁰2 g
      module γ = GroupHom γ
