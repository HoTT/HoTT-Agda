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

{- This file should be part of RephraseHigherFinCoboundary,
   but putting these in a separate file seems more effective
   in speeding up type-checking. Could be an Agda bug. -}

module cw.cohomology.RephraseHigherFinCoboundaryAbstractDefs (OT : OrdinaryTheory lzero)
  {n} (⊙fin-skel : ⊙FinSkeleton (S (S n))) where

open OrdinaryTheory OT
open import cohomology.Bouquet OT

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
function₁ <I <I₋₁ = bwproj Fin-has-dec-eq <I₋₁
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

  mega-reduction : ∀ <I <I₋₁ →
      Susp-fmap (fwproj <I₋₁) ∘ fst ⊙function₀' ∘ fwin <I
    ∼ Susp-fmap (function₁' <I <I₋₁)
  mega-reduction <I <I₋₁ = Susp-elim idp idp λ x → ↓-='-in' $ ! $
    ap (Susp-fmap (fwproj <I₋₁) ∘ fst ⊙function₀ ∘ fwin <I) (merid x)
      =⟨ ap-∘
          ( Susp-fmap (fwproj <I₋₁)
          ∘ Susp-fmap (<– (Bouquet-equiv-Xₙ/Xₙ₋₁ skel₋₁))
          ∘ cw-∂-before-Susp)
          (Bouquet-to-Xₙ/Xₙ₋₁ skel ∘ fwin <I)
          (merid x) ⟩
    ap ( Susp-fmap (fwproj <I₋₁)
       ∘ Susp-fmap (<– (Bouquet-equiv-Xₙ/Xₙ₋₁ skel₋₁))
       ∘ cw-∂-before-Susp)
       (ap (Bouquet-to-Xₙ/Xₙ₋₁ skel ∘ fwin <I) (merid x))
      =⟨ ap (ap ( Susp-fmap (fwproj <I₋₁)
                ∘ Susp-fmap (<– (Bouquet-equiv-Xₙ/Xₙ₋₁ skel₋₁))
                ∘ cw-∂-before-Susp))
            (Bouquet-to-Xₙ/Xₙ₋₁-in-merid-β skel <I x) ⟩
    ap ( Susp-fmap (fwproj <I₋₁)
       ∘ Susp-fmap (<– (Bouquet-equiv-Xₙ/Xₙ₋₁ skel₋₁))
       ∘ cw-∂-before-Susp)
       (cfglue (attaching-last skel <I x) ∙' ap cfcod (spoke <I x))
      =⟨ ap-∘
          ( Susp-fmap (fwproj <I₋₁)
          ∘ Susp-fmap (<– (Bouquet-equiv-Xₙ/Xₙ₋₁ skel₋₁)))
          cw-∂-before-Susp
          (cfglue (attaching-last skel <I x) ∙' ap cfcod (spoke <I x)) ⟩
    ap ( Susp-fmap (fwproj <I₋₁)
       ∘ Susp-fmap (<– (Bouquet-equiv-Xₙ/Xₙ₋₁ skel₋₁)))
       (ap cw-∂-before-Susp
         (cfglue (attaching-last skel <I x) ∙' ap cfcod (spoke <I x)))
      =⟨ ap (ap ( Susp-fmap (fwproj <I₋₁)
                ∘ Susp-fmap (<– (Bouquet-equiv-Xₙ/Xₙ₋₁ skel₋₁))))
            ( ap-∙' cw-∂-before-Susp (cfglue (attaching-last skel <I x)) (ap cfcod (spoke <I x))
            ∙ ap2 _∙'_
                (cw-∂-before-Susp-glue-β (attaching-last skel <I x))
                ( ∘-ap cw-∂-before-Susp cfcod (spoke <I x)
                ∙ ap-cst south (spoke <I x))) ⟩
    ap ( Susp-fmap (fwproj <I₋₁)
       ∘ Susp-fmap (<– (Bouquet-equiv-Xₙ/Xₙ₋₁ skel₋₁)))
       (merid (cfcod (attaching-last skel <I x)))
      =⟨ ap-∘
          (Susp-fmap (fwproj <I₋₁))
          (Susp-fmap (<– (Bouquet-equiv-Xₙ/Xₙ₋₁ skel₋₁)))
          (merid (cfcod (attaching-last skel <I x))) ⟩
    ap (Susp-fmap (fwproj <I₋₁))
       (ap (Susp-fmap (<– (Bouquet-equiv-Xₙ/Xₙ₋₁ skel₋₁)))
           (merid (cfcod (attaching-last skel <I x))))
      =⟨ ap
          (ap (Susp-fmap (fwproj <I₋₁)))
          (SuspFmap.merid-β
            (<– (Bouquet-equiv-Xₙ/Xₙ₋₁ skel₋₁))
            (cfcod (attaching-last skel <I x))) ⟩
    ap (Susp-fmap (fwproj <I₋₁))
       (merid (<– (Bouquet-equiv-Xₙ/Xₙ₋₁ skel₋₁) (cfcod (attaching-last skel <I x))))
      =⟨ SuspFmap.merid-β (fwproj <I₋₁)
          (<– (Bouquet-equiv-Xₙ/Xₙ₋₁ skel₋₁) (cfcod (attaching-last skel <I x))) ⟩
    merid (function₁ <I <I₋₁ x)
      =⟨ ! $ SuspFmap.merid-β (function₁ <I <I₋₁) x ⟩
    ap (Susp-fmap (function₁ <I <I₋₁)) (merid x)
      =∎
