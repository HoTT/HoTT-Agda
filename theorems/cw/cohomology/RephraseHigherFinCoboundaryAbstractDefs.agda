{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import HoTT
open import homotopy.Bouquet
open import homotopy.FinWedge
open import homotopy.SphereEndomorphism
open import groups.SphereEndomorphism
open import cw.CW
open import cw.FinCW
open import cw.WedgeOfCells
open import cw.DegreeByProjection {lzero}
open import cohomology.Theory

{- This file should be part of RephraseFinCoboundary,
   but putting these in a separate file seems more effective
   in speeding up type-checking. Could be an Agda bug. -}

module cw.cohomology.RephraseHigherFinCoboundaryAbstractDefs (OT : OrdinaryTheory lzero)
  {n} (⊙fin-skel : ⊙FinSkeleton (S (S n))) where

open OrdinaryTheory OT
open import cohomology.Bouquet OT
open import cohomology.FinBouquet OT
open import cohomology.RephraseFinCoboundary OT

private
  ⊙skel = ⊙FinSkeleton-realize ⊙fin-skel
  fin-skel = ⊙FinSkeleton.skel ⊙fin-skel
  I = AttachedFinSkeleton.numCells fin-skel
  skel = ⊙Skeleton.skel ⊙skel
  dec = ⊙FinSkeleton-has-cells-with-dec-eq ⊙fin-skel

  ⊙fin-skel₋₁ = ⊙fcw-init ⊙fin-skel
  ⊙skel₋₁ = ⊙FinSkeleton-realize ⊙fin-skel₋₁
  fin-skel₋₁ = ⊙FinSkeleton.skel ⊙fin-skel₋₁
  I₋₁ = AttachedFinSkeleton.numCells fin-skel₋₁
  skel₋₁ = ⊙Skeleton.skel ⊙skel₋₁
  dec₋₁ = ⊙FinSkeleton-has-cells-with-dec-eq ⊙fin-skel₋₁

open import cw.cohomology.HigherCoboundary OT ⊙skel
open import cw.cohomology.WedgeOfCells OT

⊙function₀ : ⊙FinBouquet I (S (S n)) ⊙→ ⊙Susp (⊙FinBouquet I₋₁ (S n))
⊙function₀ = ⊙Susp-fmap (⊙<– (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel₋₁))
          ⊙∘ ⊙cw-∂-before-Susp
          ⊙∘ ⊙–> (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel)

function₁ : Fin I → Fin I₋₁ → Sphere-endo (S n)
function₁ <I <I₋₁ = bwproj (cells-last-has-dec-eq skel₋₁ dec₋₁) (FinBouquet-family _ (S n)) <I₋₁
                  ∘ <– (Bouquet-equiv-Xₙ/Xₙ₋₁ skel₋₁)
                  ∘ cfcod
                  ∘ attaching-last skel <I

abstract
  ⊙function₀' : ⊙FinBouquet I (S (S n)) ⊙→ ⊙Susp (⊙FinBouquet I₋₁ (S n))
  ⊙function₀' = ⊙function₀

  ⊙function₀'-β : ⊙function₀' == ⊙function₀
  ⊙function₀'-β = idp

  function₁' : Fin I → Fin I₋₁ → Sphere-endo (S n)
  function₁' = function₁

  function₁'-β : ∀ <I <I₋₁ → function₁' <I <I₋₁ == function₁ <I <I₋₁
  function₁'-β _ _ = idp

postulate
  mega-reduction : ∀ <I <I₋₁ →
      Susp-fmap (fwproj <I₋₁) ∘ fst ⊙function₀' ∘ fwin <I
    ∼ Susp-fmap (function₁' <I <I₋₁)          
