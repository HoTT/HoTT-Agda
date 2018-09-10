{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cw.CW
open import cw.FinCW
open import cw.FinBoundary
open import cohomology.Theory

module cw.cohomology.cochainequiv.DualizedHigherBoundary (OT : OrdinaryTheory lzero)
  {n} (⊙fin-skel : ⊙FinSkeleton (S (S n))) where

open OrdinaryTheory OT

private
  fin-skel = ⊙FinSkeleton.skel ⊙fin-skel
  I = AttachedFinSkeleton.numCells fin-skel

  fin-skel₋₁ = AttachedFinSkeleton.skel fin-skel
  I₋₁ = AttachedFinSkeleton.numCells fin-skel₋₁

  module FAG   = FreeAbelianGroup (Fin I)
  module FAG₋₁ = FreeAbelianGroup (Fin I₋₁)

  open FAG   renaming (FreeAbGroup to G)   using ()
  open FAG₋₁ renaming (FreeAbGroup to G₋₁) using ()

abstract
  rephrase-dualized-higher-boundary-in-degree : ∀ (g : Fin I₋₁ → Group.El (C2 0)) <I
    → GroupIso.g (FAG.Freeness.extend-iso (C2-abgroup 0))
        (GroupIso.f (FAG₋₁.Freeness.extend-iso (C2-abgroup 0)) g ∘ᴳ fboundary-last fin-skel) <I
    == Group.sum (C2 0) (λ <I₋₁ → Group.exp (C2 0) (g <I₋₁) (fdegree-last fin-skel <I <I₋₁))
  rephrase-dualized-higher-boundary-in-degree g <I =
    γ.f (GroupHom.f (fboundary-last fin-skel) (FAG.insert <I))
      =⟨ ap γ.f $ app= (is-equiv.g-f (snd (FAG.Freeness.extend-equiv G₋₁)) (fboundary'-last fin-skel)) <I ⟩
    γ.f (G₋₁.sum (λ <I₋₁ → G₋₁.exp (FAG₋₁.insert <I₋₁) (deg <I₋₁)))
      =⟨ γ.pres-sum (λ <I₋₁ → G₋₁.exp (FAG₋₁.insert <I₋₁) (deg <I₋₁)) ⟩
    C⁰2.sum (λ <I₋₁ → γ.f (G₋₁.exp (FAG₋₁.insert <I₋₁) (deg <I₋₁)))
      =⟨ ap C⁰2.sum (λ= $ λ <I₋₁ → γ.pres-exp (FAG₋₁.insert <I₋₁) (deg <I₋₁)) ⟩
    C⁰2.sum (λ <I₋₁ → C⁰2.exp (γ.f (FAG₋₁.insert <I₋₁)) (deg <I₋₁))
      =⟨ ap C⁰2.sum
          (λ= λ <I₋₁ → ap (λ g → C⁰2.exp g (deg <I₋₁)) $
            app= (is-equiv.g-f (snd (FAG₋₁.Freeness.extend-equiv C⁰2)) g) <I₋₁) ⟩
    C⁰2.sum (λ <I₋₁ → C⁰2.exp (g <I₋₁) (deg <I₋₁))
      =∎
    where
      deg : Fin I₋₁ → ℤ
      deg <I₋₁ = fdegree-last fin-skel <I <I₋₁
      C⁰2 : AbGroup lzero
      C⁰2 = C2-abgroup 0
      module C⁰2 = AbGroup C⁰2
      γ : G₋₁.grp →ᴳ C⁰2.grp
      γ = FAG₋₁.Freeness.extend C⁰2 g
      module γ = GroupHom γ
