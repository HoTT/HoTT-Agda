{-# OPTIONS --without-K --rewriting #-}

open import HoTT renaming (pt to ⊙pt)
open import homotopy.Bouquet
open import homotopy.FinWedge
open import homotopy.SphereEndomorphism
open import homotopy.DisjointlyPointedSet
open import groups.SphereEndomorphism
open import groups.SumOfSubIndicator
open import groups.DisjointlyPointedSet
open import cw.CW
open import cw.DegreeByProjection
open import cw.FinBoundary
open import cw.FinCW
open import cw.WedgeOfCells
open import cohomology.Theory

module cw.cohomology.cochainequiv.FirstCoboundary (OT : OrdinaryTheory lzero)
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

open DegreeAtOne skel dec
open import cw.cohomology.WedgeOfCells OT ⊙skel
open import cw.cohomology.reconstructed.TipAndAugment OT (⊙cw-init ⊙skel)
open import cw.cohomology.reconstructed.TipCoboundary OT ⊙skel
open import cw.cohomology.cochainequiv.FirstCoboundaryAbstractDefs OT ⊙fin-skel

abstract
  rephrase-cw-co∂-head'-in-degree : ∀ g
    → GroupIso.f (CXₙ/Xₙ₋₁-diag-β ac) (GroupHom.f cw-co∂-head' (GroupIso.g (CX₀-diag-β ac₋₁) g))
    ∼ λ <I → Group.subsum-r (C2 0) ⊙head-separate
        (λ b → Group.exp (C2 0) (g b) (degree <I (fst b)))
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
          (CEl-fmap 1 (⊙Susp-fmap (<– (Bouquet-equiv-X ⊙head-is-separable)))
            (<– (CEl-Susp 0 (⊙Bouquet (MinusPoint ⊙head) 0))
              (GroupIso.g (C-SubFinBouquet-diag 0 MinusPoint-⊙head-has-choice ⊙head-separate)
                g))))) <I
      =⟨ ap (λ g → GroupIso.f (C-FinBouquet-diag 1 I) g <I) $
            ∘-CEl-fmap 1 (⊙–> (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel)) ⊙cw-∂-head'-before-Susp
              (CEl-fmap 1 (⊙Susp-fmap (<– (Bouquet-equiv-X ⊙head-is-separable)))
                (<– (CEl-Susp 0 (⊙Bouquet (MinusPoint ⊙head) 0))
                  (GroupIso.g (C-SubFinBouquet-diag 0 MinusPoint-⊙head-has-choice ⊙head-separate)
                    g)))
          ∙ ∘-CEl-fmap 1
              (⊙cw-∂-head'-before-Susp ⊙∘ ⊙–> (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel))
              (⊙Susp-fmap (<– (Bouquet-equiv-X ⊙head-is-separable)))
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
          (⊙Susp-fmap (bwproj MinusPoint-⊙head-has-dec-eq b) ⊙∘ ⊙function₀' ⊙∘ ⊙fwin <I)))
      =⟨ ap (Group.subsum-r (C2 0) ⊙head-separate)
          (λ= λ b → ap (Group.exp (C2 0) (g b)) $
            ⊙SphereS-endo-degree-base-indep 0
              {f = (  ⊙Susp-fmap (bwproj MinusPoint-⊙head-has-dec-eq b)
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
            degree-matches <I b) ⟩
    Group.subsum-r (C2 0) ⊙head-separate
      (λ b → Group.exp (C2 0) (g b)
        (degree <I (fst b)))
      =∎

abstract
  private
    degree-true-≠ : ∀ {<I <I₋₁} → (<I₋₁ ≠ endpoint <I true) → degree-true <I <I₋₁ == 0
    degree-true-≠ {<I} {<I₋₁} neq with Fin-has-dec-eq <I₋₁ (endpoint <I true)
    ... | inl eq = ⊥-rec (neq eq)
    ... | inr _ = idp

    degree-true-diag : ∀ <I → degree-true <I (endpoint <I true) == -1
    degree-true-diag <I with Fin-has-dec-eq (endpoint <I true) (endpoint <I true)
    ... | inl _ = idp
    ... | inr neq = ⊥-rec (neq idp)

    sum-degree-true : ∀ <I g → Group.sum (C2 0) (λ <I₋₁ → Group.exp (C2 0) g (degree-true <I <I₋₁)) == Group.inv (C2 0) g
    sum-degree-true <I g =
        sum-subindicator (C2 0) (λ <I₋₁ → Group.exp (C2 0) g (degree-true <I <I₋₁))
          (endpoint <I true) (λ neq → ap (Group.exp (C2 0) g) (degree-true-≠ neq))
      ∙ ap (Group.exp (C2 0) g) (degree-true-diag <I)

    degree-false-≠ : ∀ {<I <I₋₁} → (<I₋₁ ≠ endpoint <I false) → degree-false <I <I₋₁ == 0
    degree-false-≠ {<I} {<I₋₁} neq with Fin-has-dec-eq <I₋₁ (endpoint <I false)
    ... | inl eq = ⊥-rec (neq eq)
    ... | inr _ = idp

    degree-false-diag : ∀ <I → degree-false <I (endpoint <I false) == 1
    degree-false-diag <I with Fin-has-dec-eq (endpoint <I false) (endpoint <I false)
    ... | inl _ = idp
    ... | inr neq = ⊥-rec (neq idp)

    sum-degree-false : ∀ <I g → Group.sum (C2 0) (λ <I₋₁ → Group.exp (C2 0) g (degree-false <I <I₋₁)) == g
    sum-degree-false <I g =
        sum-subindicator (C2 0) (λ <I₋₁ → Group.exp (C2 0) g (degree-false <I <I₋₁))
          (endpoint <I false) (λ neq → ap (Group.exp (C2 0) g) (degree-false-≠ neq))
      ∙ ap (Group.exp (C2 0) g) (degree-false-diag <I)

    sum-degree : ∀ <I g → Group.sum (C2 0) (λ <I₋₁ → Group.exp (C2 0) g (degree <I <I₋₁)) == Group.ident (C2 0)
    sum-degree <I g =
        ap (Group.sum (C2 0)) (λ= λ <I₋₁ → Group.exp-+ (C2 0) g (degree-true <I <I₋₁) (degree-false <I <I₋₁))
      ∙ AbGroup.sum-comp (C2-abgroup 0)
          (λ <I₋₁ → Group.exp (C2 0) g (degree-true <I <I₋₁))
          (λ <I₋₁ → Group.exp (C2 0) g (degree-false <I <I₋₁))
      ∙ ap2 (Group.comp (C2 0))
          (sum-degree-true <I g)
          (sum-degree-false <I g)
      ∙ Group.inv-l (C2 0) g

    merge-branches : ∀ (g : Fin I₋₁ → Group.El (C2 0)) (g-pt : g pt == Group.ident (C2 0)) x
      →  Coprod-rec (λ _ → Group.ident (C2 0)) (λ b → g (fst b)) (⊙head-separate x)
      == g x
    merge-branches g g-pt x with Fin-has-dec-eq pt x
    merge-branches g g-pt x | inl idp = ! g-pt
    merge-branches g g-pt x | inr _ = idp

  rephrase-cw-co∂-head-in-degree : ∀ g
    → GroupIso.f (CXₙ/Xₙ₋₁-diag-β ac) (GroupHom.f cw-co∂-head (GroupIso.g (C2×CX₀-diag-β ac₋₁) g))
    ∼ λ <I → Group.sum (C2 0) (λ <I₋₁ → Group.exp (C2 0) (g <I₋₁) (degree <I <I₋₁))
  rephrase-cw-co∂-head-in-degree g <I =
    GroupIso.f (CXₙ/Xₙ₋₁-diag-β ac) (GroupHom.f cw-co∂-head' (GroupIso.g (CX₀-diag-β ac₋₁) (snd (diff-and-separate (C2 0) g)))) <I
      =⟨ rephrase-cw-co∂-head'-in-degree (snd (diff-and-separate (C2 0) g)) <I ⟩
    Group.subsum-r (C2 0) ⊙head-separate
      (λ b → Group.exp (C2 0) (Group.diff (C2 0) (g (fst b)) (g pt))
        (degree <I (fst b)))
      =⟨ ap (Group.sum (C2 0)) (λ= λ <I₋₁ →
          merge-branches
            (λ <I₋₁ → Group.exp (C2 0) (Group.diff (C2 0) (g <I₋₁) (g pt)) (degree <I <I₋₁))
            ( ap (λ g → Group.exp (C2 0) g (degree <I pt)) (Group.inv-r (C2 0) (g pt))
            ∙ Group.exp-ident (C2 0) (degree <I pt))
            <I₋₁
          ∙ AbGroup.exp-comp (C2-abgroup 0) (g <I₋₁) (Group.inv (C2 0) (g pt)) (degree <I <I₋₁)) ⟩
    Group.sum (C2 0) (λ <I₋₁ →
      Group.comp (C2 0)
        (Group.exp (C2 0) (g <I₋₁) (degree <I <I₋₁))
        (Group.exp (C2 0) (Group.inv (C2 0) (g pt)) (degree <I <I₋₁)))
      =⟨ AbGroup.sum-comp (C2-abgroup 0)
          (λ <I₋₁ → Group.exp (C2 0) (g <I₋₁) (degree <I <I₋₁))
          (λ <I₋₁ → Group.exp (C2 0) (Group.inv (C2 0) (g pt)) (degree <I <I₋₁)) ⟩
    Group.comp (C2 0)
      (Group.sum (C2 0) (λ <I₋₁ → Group.exp (C2 0) (g <I₋₁) (degree <I <I₋₁)))
      (Group.sum (C2 0) (λ <I₋₁ → Group.exp (C2 0) (Group.inv (C2 0) (g pt)) (degree <I <I₋₁)))
      =⟨ ap (Group.comp (C2 0) (Group.sum (C2 0) (λ <I₋₁ → Group.exp (C2 0) (g <I₋₁) (degree <I <I₋₁))))
          (sum-degree <I (Group.inv (C2 0) (g pt)))
        ∙ Group.unit-r (C2 0) _ ⟩
    Group.sum (C2 0) (λ <I₋₁ → Group.exp (C2 0) (g <I₋₁) (degree <I <I₋₁))
      =∎
