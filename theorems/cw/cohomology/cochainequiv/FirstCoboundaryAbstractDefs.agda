{-# OPTIONS --without-K --rewriting #-}

open import HoTT renaming (pt to ⊙pt)
open import homotopy.Bouquet
open import homotopy.FinWedge
open import homotopy.LoopSpaceCircle
open import homotopy.SphereEndomorphism
open import groups.SphereEndomorphism
open import cw.CW
open import cw.FinCW
open import cw.WedgeOfCells
open import cw.DegreeByProjection {lzero}
open import homotopy.DisjointlyPointedSet
open import cohomology.Theory

module cw.cohomology.cochainequiv.FirstCoboundaryAbstractDefs (OT : OrdinaryTheory lzero)
  (⊙fin-skel : ⊙FinSkeleton 1) where

open OrdinaryTheory OT
open import cohomology.Bouquet OT

private
  ⊙skel = ⊙FinSkeleton-realize ⊙fin-skel
  fin-skel = ⊙FinSkeleton.skel ⊙fin-skel
  I = AttachedFinSkeleton.numCells fin-skel
  skel = ⊙Skeleton.skel ⊙skel
  dec = FinSkeleton-has-cells-with-dec-eq fin-skel

  endpoint = attaching-last skel
  I₋₁ = AttachedFinSkeleton.skel fin-skel
  ⊙head = ⊙cw-head ⊙skel
  pt = ⊙pt ⊙head

open import cw.cohomology.reconstructed.TipCoboundary OT ⊙skel


⊙head-is-separable : is-separable ⊙head
⊙head-is-separable = Fin-has-dec-eq pt

⊙head-separate = separate-pt ⊙head-is-separable

⊙head-separate-equiv = (unite-pt ⊙head , separable-has-disjoint-pt ⊙head-is-separable)⁻¹

MinusPoint-⊙head-has-choice : has-choice 0 (MinusPoint ⊙head) lzero
MinusPoint-⊙head-has-choice = MinusPoint-has-choice ⊙head-is-separable (Fin-has-choice 0 lzero)

MinusPoint-⊙head-has-dec-eq : has-dec-eq (MinusPoint ⊙head)
MinusPoint-⊙head-has-dec-eq = MinusPoint-has-dec-eq Fin-has-dec-eq

⊙function₀ : ⊙FinBouquet I 1 ⊙→ ⊙Susp (⊙Bouquet (MinusPoint ⊙head) 0)
⊙function₀ = ⊙Susp-fmap (⊙<– (Bouquet-⊙equiv-X ⊙head-is-separable))
          ⊙∘ ⊙cw-∂-head'-before-Susp
          ⊙∘ ⊙–> (Bouquet-⊙equiv-Xₙ/Xₙ₋₁ skel)

function₁ : Fin I → MinusPoint ⊙head → Sphere-endo 0
function₁ <I b x with Fin-has-dec-eq (fst b) (endpoint <I x)
function₁ <I b x | inl _ = false
function₁ <I b x | inr _ = true

abstract
  ⊙function₀' : ⊙FinBouquet I 1 ⊙→ ⊙Susp (⊙Bouquet (MinusPoint ⊙head) 0)
  ⊙function₀' = ⊙function₀

  ⊙function₀'-β : ⊙function₀' == ⊙function₀
  ⊙function₀'-β = idp

  function₁' : Fin I → MinusPoint ⊙head → Sphere-endo 0
  function₁' = function₁

  function₁'-β : ∀ <I b → function₁' <I b == function₁ <I b
  function₁'-β _ _ = idp

  private
    mega-reduction-cases : ∀ <I b x
      →  bwproj MinusPoint-⊙head-has-dec-eq b (<– (Bouquet-equiv-X ⊙head-is-separable) (endpoint <I x))
      == function₁ <I b x
    mega-reduction-cases <I b x with Fin-has-dec-eq pt (endpoint <I x)
    mega-reduction-cases <I b x | inl _ with Fin-has-dec-eq (fst b) (endpoint <I x)
    mega-reduction-cases <I b x | inl pt=end | inl b=end = ⊥-rec (snd b (pt=end ∙ ! b=end))
    mega-reduction-cases <I b x | inl _ | inr _ = idp
    mega-reduction-cases <I b x | inr _ with Fin-has-dec-eq (fst b) (endpoint <I x)
    mega-reduction-cases <I b x | inr _ | inl b=end =
      bwproj MinusPoint-⊙head-has-dec-eq b (bwin (endpoint <I x , _) false)
        =⟨ ap (λ b' → bwproj MinusPoint-⊙head-has-dec-eq b (bwin b' false)) $ ! $
            Subtype=-out (MinusPoint-prop ⊙head) b=end ⟩
      bwproj MinusPoint-⊙head-has-dec-eq b (bwin b false)
        =⟨ bwproj-bwin-diag MinusPoint-⊙head-has-dec-eq b false ⟩ 
      false
        =∎
    mega-reduction-cases <I b x | inr _ | inr b≠end =
      bwproj-bwin-≠ MinusPoint-⊙head-has-dec-eq (b≠end ∘ ap fst) false

  mega-reduction : ∀ <I b →
      Susp-fmap (bwproj MinusPoint-⊙head-has-dec-eq b) ∘ fst ⊙function₀' ∘ fwin <I
    ∼ Susp-fmap (function₁' <I b)
  mega-reduction <I b = Susp-elim idp idp λ x → ↓-='-in' $ ! $
    ap (Susp-fmap (bwproj MinusPoint-⊙head-has-dec-eq b) ∘ fst ⊙function₀ ∘ fwin <I) (merid x)
      =⟨ ap-∘
          ( Susp-fmap (bwproj MinusPoint-⊙head-has-dec-eq b)
          ∘ Susp-fmap (<– (Bouquet-equiv-X ⊙head-is-separable))
          ∘ cw-∂-head'-before-Susp)
          (Bouquet-to-Xₙ/Xₙ₋₁ skel ∘ fwin <I)
          (merid x) ⟩
    ap ( Susp-fmap (bwproj MinusPoint-⊙head-has-dec-eq b)
       ∘ Susp-fmap (<– (Bouquet-equiv-X ⊙head-is-separable))
       ∘ cw-∂-head'-before-Susp)
       (ap (Bouquet-to-Xₙ/Xₙ₋₁ skel ∘ fwin <I) (merid x))
      =⟨ ap (ap ( Susp-fmap (bwproj MinusPoint-⊙head-has-dec-eq b)
                ∘ Susp-fmap (<– (Bouquet-equiv-X ⊙head-is-separable))
                ∘ cw-∂-head'-before-Susp))
            (Bouquet-to-Xₙ/Xₙ₋₁-in-merid-β skel <I x) ⟩
    ap ( Susp-fmap (bwproj MinusPoint-⊙head-has-dec-eq b)
       ∘ Susp-fmap (<– (Bouquet-equiv-X ⊙head-is-separable))
       ∘ cw-∂-head'-before-Susp)
       (cfglue (endpoint <I x) ∙' ap cfcod (spoke <I x))
      =⟨ ap-∘
          ( Susp-fmap (bwproj MinusPoint-⊙head-has-dec-eq b)
          ∘ Susp-fmap (<– (Bouquet-equiv-X ⊙head-is-separable)))
          cw-∂-head'-before-Susp
          (cfglue (endpoint <I x) ∙' ap cfcod (spoke <I x)) ⟩
    ap ( Susp-fmap (bwproj MinusPoint-⊙head-has-dec-eq b)
       ∘ Susp-fmap (<– (Bouquet-equiv-X ⊙head-is-separable)))
       (ap cw-∂-head'-before-Susp
         (cfglue (endpoint <I x) ∙' ap cfcod (spoke <I x)))
      =⟨ ap (ap ( Susp-fmap (bwproj MinusPoint-⊙head-has-dec-eq b)
                ∘ Susp-fmap (<– (Bouquet-equiv-X ⊙head-is-separable))))
            ( ap-∙' cw-∂-head'-before-Susp (cfglue (endpoint <I x)) (ap cfcod (spoke <I x))
            ∙ ap2 _∙'_
                (cw-∂-head'-before-Susp-glue-β (endpoint <I x))
                ( ∘-ap cw-∂-head'-before-Susp cfcod (spoke <I x)
                ∙ ap-cst south (spoke <I x))) ⟩
    ap ( Susp-fmap (bwproj MinusPoint-⊙head-has-dec-eq b)
       ∘ Susp-fmap (<– (Bouquet-equiv-X ⊙head-is-separable)))
       (merid (endpoint <I x))
      =⟨ ap-∘
          (Susp-fmap (bwproj MinusPoint-⊙head-has-dec-eq b))
          (Susp-fmap (<– (Bouquet-equiv-X ⊙head-is-separable)))
          (merid (endpoint <I x)) ⟩
    ap (Susp-fmap (bwproj MinusPoint-⊙head-has-dec-eq b))
       (ap (Susp-fmap (<– (Bouquet-equiv-X ⊙head-is-separable)))
           (merid (endpoint <I x)))
      =⟨ ap
          (ap (Susp-fmap (bwproj MinusPoint-⊙head-has-dec-eq b)))
          (SuspFmap.merid-β
            (<– (Bouquet-equiv-X ⊙head-is-separable))
            (endpoint <I x)) ⟩
    ap (Susp-fmap (bwproj MinusPoint-⊙head-has-dec-eq b))
       (merid (<– (Bouquet-equiv-X ⊙head-is-separable) (endpoint <I x)))
      =⟨ SuspFmap.merid-β (bwproj MinusPoint-⊙head-has-dec-eq b)
          (<– (Bouquet-equiv-X ⊙head-is-separable) (endpoint <I x)) ⟩
    merid (bwproj MinusPoint-⊙head-has-dec-eq b (<– (Bouquet-equiv-X ⊙head-is-separable) (endpoint <I x)))
      =⟨ ap merid (mega-reduction-cases <I b x) ⟩
    merid (function₁ <I b x)
      =⟨ ! $ SuspFmap.merid-β (function₁ <I b) x ⟩
    ap (Susp-fmap (function₁ <I b)) (merid x)
      =∎
 
  open DegreeAtOne skel dec

  degree-matches' : ∀ <I b
    →  merid (function₁' <I b false) ∙ ! (merid (function₁' <I b true))
    == loop^ (degree <I (fst b))
  degree-matches' <I b with Fin-has-dec-eq (fst b) (endpoint <I false)
  degree-matches' <I b | inl _ with Fin-has-dec-eq (fst b) (endpoint <I true)
  degree-matches' <I b | inl _ | inl _ = !-inv-r (merid false)
  degree-matches' <I b | inl _ | inr _ = idp
  degree-matches' <I b | inr _ with Fin-has-dec-eq (fst b) (endpoint <I true)
  degree-matches' <I b | inr _ | inl _ = ap (_∙ ! (merid false)) (! (!-! (merid true))) ∙ ∙-! (! (merid true)) (merid false)
  degree-matches' <I b | inr _ | inr _ = !-inv-r (merid true)
 
  degree-matches : ∀ <I b
    →  ⊙SphereS-endo-degree 0 (Susp-fmap (function₁' <I b) , idp)
    == degree <I (fst b)
  degree-matches <I b = equiv-adj' ΩS¹-equiv-ℤ $
    ap (Susp-fmap (function₁ <I b)) loop
      =⟨ ap-∙ (Susp-fmap (function₁ <I b)) (merid false) (! (merid true))  ⟩
    ap (Susp-fmap (function₁ <I b)) (merid false)
    ∙ ap (Susp-fmap (function₁ <I b)) (! (merid true))
      =⟨ ap2 _∙_
          (SuspFmap.merid-β (function₁ <I b) false)
            ( ap-! (Susp-fmap (function₁ <I b)) (merid true)
            ∙ ap ! (SuspFmap.merid-β (function₁ <I b) true)) ⟩
    merid (function₁ <I b false) ∙ ! (merid (function₁ <I b true))
      =⟨ degree-matches' <I b ⟩
    loop^ (degree <I (fst b))
      =∎
