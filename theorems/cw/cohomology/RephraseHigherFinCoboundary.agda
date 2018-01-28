{-# OPTIONS --without-K --rewriting #-}

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

module cw.cohomology.RephraseHigherFinCoboundary (OT : OrdinaryTheory lzero)
  {n} (⊙fin-skel : ⊙FinSkeleton (S (S n))) where

open OrdinaryTheory OT
open import cohomology.FinBouquet OT
open import cohomology.RephraseFinCoboundary OT

private
  ⊙skel = ⊙FinSkeleton-realize ⊙fin-skel
  fin-skel = ⊙FinSkeleton.skel ⊙fin-skel
  I = AttachedFinSkeleton.numCells fin-skel
  skel = ⊙Skeleton.skel ⊙skel
  ac = ⊙FinSkeleton-has-cells-with-choice 0 ⊙fin-skel lzero
  dec = ⊙FinSkeleton-has-cells-with-dec-eq ⊙fin-skel

  ⊙fin-skel₋₁ = ⊙fcw-init ⊙fin-skel
  ⊙skel₋₁ = ⊙FinSkeleton-realize ⊙fin-skel₋₁
  fin-skel₋₁ = ⊙FinSkeleton.skel ⊙fin-skel₋₁
  I₋₁ = AttachedFinSkeleton.numCells fin-skel₋₁
  skel₋₁ = ⊙Skeleton.skel ⊙skel₋₁
  ac₋₁ = ⊙FinSkeleton-has-cells-with-choice 0 ⊙fin-skel₋₁ lzero
  dec₋₁ = ⊙FinSkeleton-has-cells-with-dec-eq ⊙fin-skel₋₁

open import cw.cohomology.HigherCoboundary OT ⊙skel
open import cw.cohomology.WedgeOfCells OT
open import cw.cohomology.RephraseHigherFinCoboundaryAbstractDefs OT ⊙fin-skel

abstract
  rephrase-cw-co∂-last-in-degree : ∀ g
    → GroupIso.f (CXₙ/Xₙ₋₁-diag-β ⊙skel ac) (GroupHom.f cw-co∂-last (GroupIso.g (CXₙ/Xₙ₋₁-diag-β ⊙skel₋₁ ac₋₁) g))
    ∼ λ <I → Group.sum (C2 0) (λ <I₋₁ → Group.exp (C2 0) (g <I₋₁) (degree-last skel dec <I <I₋₁))
  rephrase-cw-co∂-last-in-degree g <I =
    GroupIso.f (C-FinBouquet-diag (S (S n)) I)
      (CEl-fmap (ℕ-to-ℤ (S (S n))) (⊙–> (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel))
        (GroupHom.f cw-co∂-last
          (CEl-fmap (ℕ-to-ℤ (S n)) (⊙<– (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel₋₁))
            (GroupIso.g (C-FinBouquet-diag (S n) I₋₁)
              g)))) <I
      =⟨ ap
          (λ g →
            GroupIso.f (C-FinBouquet-diag (S (S n)) I)
              (CEl-fmap (ℕ-to-ℤ (S (S n))) (⊙–> (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel)) g) <I) $
          cw-co∂-last-β
            (CEl-fmap (ℕ-to-ℤ (S n)) (⊙<– (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel₋₁))
              (GroupIso.g (C-FinBouquet-diag (S n) I₋₁)
                g)) ⟩
    GroupIso.f (C-FinBouquet-diag (S (S n)) I)
      (CEl-fmap (ℕ-to-ℤ (S (S n))) (⊙–> (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel))
        (CEl-fmap (ℕ-to-ℤ (S (S n))) ⊙cw-∂-before-Susp
          (<– (CEl-Susp (ℕ-to-ℤ (S n)) (⊙Xₙ/Xₙ₋₁ skel₋₁))
            (CEl-fmap (ℕ-to-ℤ (S n)) (⊙<– (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel₋₁))
              (GroupIso.g (C-FinBouquet-diag (S n) I₋₁)
                g))))) <I
      =⟨ ap
          (λ g →
            GroupIso.f (C-FinBouquet-diag (S (S n)) I)
              (CEl-fmap (ℕ-to-ℤ (S (S n))) (⊙–> (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel))
                (CEl-fmap (ℕ-to-ℤ (S (S n))) ⊙cw-∂-before-Susp g)) <I) $
          C-Susp-fmap' (ℕ-to-ℤ (S n)) (⊙<– (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel₋₁)) □$ᴳ
          (GroupIso.g (C-FinBouquet-diag (S n) I₋₁)
            g) ⟩
    GroupIso.f (C-FinBouquet-diag (S (S n)) I)
      (CEl-fmap (ℕ-to-ℤ (S (S n))) (⊙–> (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel))
        (CEl-fmap (ℕ-to-ℤ (S (S n))) ⊙cw-∂-before-Susp
          (CEl-fmap (ℕ-to-ℤ (S (S n))) (⊙Susp-fmap (⊙<– (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel₋₁)))
            (<– (CEl-Susp (ℕ-to-ℤ (S n)) (⊙FinBouquet _ (S n)))
              (GroupIso.g (C-FinBouquet-diag (S n) I₋₁)
                g))))) <I
      =⟨ ap (λ g → GroupIso.f (C-FinBouquet-diag (S (S n)) I) g <I) $
            ∘-CEl-fmap (ℕ-to-ℤ (S (S n))) (⊙–> (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel)) ⊙cw-∂-before-Susp
              (CEl-fmap (ℕ-to-ℤ (S (S n))) (⊙Susp-fmap (⊙<– (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel₋₁)))
                (<– (CEl-Susp (ℕ-to-ℤ (S n)) (⊙FinBouquet _ (S n)))
                  (GroupIso.g (C-FinBouquet-diag (S n) I₋₁)
                    g)))
          ∙ ∘-CEl-fmap (ℕ-to-ℤ (S (S n)))
              (⊙cw-∂-before-Susp ⊙∘ ⊙–> (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel))
              (⊙Susp-fmap (⊙<– (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel₋₁)))
              (<– (CEl-Susp (ℕ-to-ℤ (S n)) (⊙FinBouquet _ (S n)))
                (GroupIso.g (C-FinBouquet-diag (S n) I₋₁)
                  g))      
          ∙ ap (λ f → CEl-fmap (ℕ-to-ℤ (S (S n))) f
              (<– (CEl-Susp (ℕ-to-ℤ (S n)) (⊙FinBouquet _ (S n)))
                (GroupIso.g (C-FinBouquet-diag (S n) I₋₁)
                  g)))
              (! ⊙function₀'-β) ⟩
    GroupIso.f (C-FinBouquet-diag (S (S n)) I)
      (CEl-fmap (ℕ-to-ℤ (S (S n))) ⊙function₀'
        (<– (CEl-Susp (ℕ-to-ℤ (S n)) (⊙FinBouquet _ (S n)))
          (GroupIso.g (C-FinBouquet-diag (S n) I₋₁)
            g))) <I
      =⟨ rephrase-in-degree (S n) {I = I} {J = I₋₁} ⊙function₀' g <I ⟩
    Group.sum (C2 0)
      (λ <I₋₁ → Group.exp (C2 0) (g <I₋₁)
        (⊙SphereS-endo-degree (S n)
          (⊙Susp-fmap (⊙fwproj <I₋₁) ⊙∘ ⊙function₀' ⊙∘ ⊙fwin <I)))
      =⟨ ap (Group.sum (C2 0))
          (λ= λ <I₋₁ → ap (Group.exp (C2 0) (g <I₋₁)) $
            ⊙SphereS-endo-degree-base-indep (S n)
              {f = (  ⊙Susp-fmap (⊙fwproj <I₋₁)
                   ⊙∘ ⊙function₀'
                   ⊙∘ ⊙fwin <I)}
              {g = (Susp-fmap (function₁' <I <I₋₁) , idp)}
              (mega-reduction <I <I₋₁)) ⟩
    Group.sum (C2 0)
      (λ <I₋₁ → Group.exp (C2 0) (g <I₋₁)
        (⊙SphereS-endo-degree (S n)
          (Susp-fmap (function₁' <I <I₋₁) , idp)))
      =⟨ ap (Group.sum (C2 0))
          (λ= λ <I₋₁ → ap (Group.exp (C2 0) (g <I₋₁)) $
            ⊙SphereS-endo-degree-Susp' n (function₁' <I <I₋₁)) ⟩
    Group.sum (C2 0)
      (λ <I₋₁ → Group.exp (C2 0) (g <I₋₁)
        (Trunc-⊙SphereS-endo-degree n
          (Trunc-⊙SphereS-endo-in n
            [ function₁' <I <I₋₁ ])))
      =⟨ ap (Group.sum (C2 0))
          (λ= λ <I₋₁ → ap
            (λ f → Group.exp (C2 0) (g <I₋₁)
              (Trunc-⊙SphereS-endo-degree n
                (Trunc-⊙SphereS-endo-in n
                  [ f ])))
            (function₁'-β <I <I₋₁)) ⟩
    Group.sum (C2 0)
      (λ <I₋₁ → Group.exp (C2 0) (g <I₋₁)
        (Trunc-⊙SphereS-endo-degree n
          (Trunc-⊙SphereS-endo-in n
            [ function₁ <I <I₋₁ ])))
      =∎
