{-# OPTIONS --without-K --rewriting #-}

open import HoTT renaming (pt to ⊙pt)
open import homotopy.Bouquet
open import homotopy.FinWedge
open import homotopy.SphereEndomorphism
open import homotopy.DisjointlyPointedSet
open import groups.SphereEndomorphism
open import cw.CW
open import cw.FinCW
open import cw.WedgeOfCells
open import cw.FinBoundary
open import cohomology.Theory

module cw.cohomology.RephraseFirstFinCoboundary (OT : OrdinaryTheory lzero)
  (⊙fin-skel : ⊙FinSkeleton 1) where

open OrdinaryTheory OT
open import cohomology.RephraseSubFinCoboundary OT
open import cohomology.SubFinBouquet OT

private
  ⊙skel = ⊙FinSkeleton-realize ⊙fin-skel
  fin-skel = ⊙FinSkeleton.skel ⊙fin-skel
  I = AttachedFinSkeleton.numCells fin-skel
  skel = ⊙Skeleton.skel ⊙skel
  dec = FinSkeleton-has-cells-with-dec-eq fin-skel
  ac = FinSkeleton-has-cells-with-choice 0 fin-skel lzero

  fin-skel₋₁ = fcw-init fin-skel
  ac₋₁ = FinSkeleton-has-cells-with-choice 0 fin-skel₋₁ lzero
  endpoint = attaching-last skel
  I₋₁ = AttachedFinSkeleton.skel fin-skel
  ⊙head = ⊙cw-head ⊙skel
  pt = ⊙pt ⊙head

open import cw.cohomology.TipAndAugment OT (⊙cw-init ⊙skel)
open import cw.cohomology.TipCoboundary OT ⊙skel
open import cw.cohomology.WedgeOfCells OT ⊙skel
open import cw.cohomology.RephraseFirstFinCoboundaryAbstractDefs OT ⊙fin-skel

abstract
  rephrase-cw-co∂-head'-in-degree : ∀ g
    → GroupIso.f (CXₙ/Xₙ₋₁-diag-β ac) (GroupHom.f cw-co∂-head' (GroupIso.g (CX₀-diag-β ac₋₁) g))
    ∼ λ <I → Group.subsum-r (C2 0) ⊙head-separate
        (λ b → Group.exp (C2 0) (g b) (fdegree-last fin-skel <I (fst b)))
  rephrase-cw-co∂-head'-in-degree g <I =
    GroupIso.f (C-FinBouquet-diag 1 I)
      (CEl-fmap 1 (⊙–> (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel))
        (CEl-fmap 1 ⊙cw-∂-head'-before-Susp
          (<– (CEl-Susp 0 ⊙head)
            (CEl-fmap 0 (⊙<– (Bouquet-⊙equiv-X ⊙head-is-separable))
              (GroupIso.g (C-SubFinBouquet-diag 0 MinusPoint-⊙head-has-choice ⊙head-separate)
                g))))) <I
      =⟨ ap
          (λ g →
            GroupIso.f (C-FinBouquet-diag 1 I)
              (CEl-fmap 1 (⊙–> (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel))
                (CEl-fmap 1 ⊙cw-∂-head'-before-Susp g)) <I) $
          C-Susp-fmap' 0 (⊙<– (Bouquet-⊙equiv-X (Fin-has-dec-eq pt))) □$ᴳ
            (GroupIso.g (C-SubFinBouquet-diag 0 MinusPoint-⊙head-has-choice ⊙head-separate)
              g) ⟩
    GroupIso.f (C-FinBouquet-diag 1 I)
      (CEl-fmap 1 (⊙–> (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel))
        (CEl-fmap 1 ⊙cw-∂-head'-before-Susp
          (CEl-fmap 1 (⊙Susp-fmap (⊙<– (Bouquet-⊙equiv-X ⊙head-is-separable)))
            (<– (CEl-Susp 0 (⊙Bouquet (MinusPoint ⊙head) 0))
              (GroupIso.g (C-SubFinBouquet-diag 0 MinusPoint-⊙head-has-choice ⊙head-separate)
                g))))) <I
      =⟨ ap (λ g → GroupIso.f (C-FinBouquet-diag 1 I) g <I) $
            ∘-CEl-fmap 1 (⊙–> (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel)) ⊙cw-∂-head'-before-Susp
              (CEl-fmap 1 (⊙Susp-fmap (⊙<– (Bouquet-⊙equiv-X ⊙head-is-separable)))
                (<– (CEl-Susp 0 (⊙Bouquet (MinusPoint ⊙head) 0))
                  (GroupIso.g (C-SubFinBouquet-diag 0 MinusPoint-⊙head-has-choice ⊙head-separate)
                    g)))
          ∙ ∘-CEl-fmap 1
              (⊙cw-∂-head'-before-Susp ⊙∘ ⊙–> (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel))
              (⊙Susp-fmap (⊙<– (Bouquet-⊙equiv-X ⊙head-is-separable)))
              (<– (CEl-Susp 0 (⊙Bouquet (MinusPoint ⊙head) 0))
                (GroupIso.g (C-SubFinBouquet-diag 0 MinusPoint-⊙head-has-choice ⊙head-separate)
                  g))
          ∙ ap (λ f → CEl-fmap 1 f
              (<– (CEl-Susp 0 (⊙Bouquet (MinusPoint ⊙head) 0))
                (GroupIso.g (C-SubFinBouquet-diag 0 MinusPoint-⊙head-has-choice ⊙head-separate)
                  g)))
              (! ⊙function₀'-β) ⟩
    GroupIso.f (C-FinBouquet-diag 1 I)
      (CEl-fmap 1 ⊙function₀'
        (<– (CEl-Susp 0 (⊙Bouquet (MinusPoint ⊙head) 0))
          (GroupIso.g (C-SubFinBouquet-diag 0 MinusPoint-⊙head-has-choice ⊙head-separate)
            g))) <I
      =⟨ rephrase-in-degree 0 {I = I} MinusPoint-⊙head-has-choice
          MinusPoint-⊙head-has-dec-eq ⊙head-separate-equiv ⊙function₀' g <I ⟩
    Group.subsum-r (C2 0) ⊙head-separate
      (λ b → Group.exp (C2 0) (g b)
        (⊙SphereS-endo-degree 0
          (⊙Susp-fmap (⊙bwproj MinusPoint-⊙head-has-dec-eq b) ⊙∘ ⊙function₀' ⊙∘ ⊙fwin <I)))
      =⟨ ap (Group.subsum-r (C2 0) ⊙head-separate)
          (λ= λ b → ap (Group.exp (C2 0) (g b)) $
            ⊙SphereS-endo-degree-base-indep 0
              {f = (  ⊙Susp-fmap (⊙bwproj MinusPoint-⊙head-has-dec-eq b)
                   ⊙∘ ⊙function₀'
                   ⊙∘ ⊙fwin <I)}
              {g = (Susp-fmap (function₁' <I b) , idp)}
              (mega-reduction <I b)) ⟩
    Group.subsum-r (C2 0) ⊙head-separate
      (λ b → Group.exp (C2 0) (g b)
        (⊙SphereS-endo-degree 0
          (Susp-fmap (function₁' <I b) , idp)))
      =⟨ ap (Group.subsum-r (C2 0) ⊙head-separate)
          (λ= λ b → ap (Group.exp (C2 0) (g b)) $
            maha-reduction <I b) ⟩
    Group.subsum-r (C2 0) ⊙head-separate
      (λ b → Group.exp (C2 0) (g b)
        (fdegree-last fin-skel <I (fst b)))
      =∎
