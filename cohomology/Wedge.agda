{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.CofiberSequence
open import cohomology.Exactness
open import cohomology.FunctionOver
open import cohomology.OrdinaryTheory
open import cohomology.ProductRepr

{- Finite additivity is provable (and in a stronger form) without using
 - the additivity axiom. For any m ≥ 0,

         Cₙ(Σᵐ(X ∨ Y)) == Cₙ(ΣᵐX) × Cₙ(ΣᵐY)

 - and over this path
 -   ∙ Cₙ(Σᵐwinl) corresponds to fst : Cₙ(ΣᵐX) × Cₙ(ΣᵐY) → Cₙ(ΣᵐX),
 -   ∙ Cₙ(Σᵐwinr) corresponds to snd : Cₙ(ΣᵐX) × Cₙ(ΣᵐY) → Cₙ(ΣᵐY),
 -   ∙ Cₙ(Σᵐ(Wedge-rec winl* winr* wglue*)) : Cₙ(ΣᵐZ) → Cₙ(Σᵐ(X ∨ Y))
       corresponds to Cₙ(Σᵐwinl*) × Cₙ(Σᵐwinr*).
 -}

module cohomology.Wedge {i} (OT : OrdinaryTheory i) (n : ℤ) {X Y : Ptd i} where

open import cohomology.WedgeCofiber {X = X} {Y = Y}

open OrdinaryTheory OT
open import cohomology.ConstantFunction OT

module _ (m : ℕ) where

  βl : CF-hom n (ptd-susp^-fmap m ptd-winl) ∘hom
       CF-hom n (ptd-susp^-fmap m ptd-projl)
       == idhom _
  βl = ! (CF-comp n (ptd-susp^-fmap m ptd-projl)
                     (ptd-susp^-fmap m ptd-winl))
       ∙ ap (CF-hom n)
            (! (ptd-susp^-fmap-∘ m ptd-projl ptd-winl)
             ∙ ptd-susp^-fmap-idf m _)
       ∙ CF-ident n

  βr : CF-hom n (ptd-susp^-fmap m ptd-winr) ∘hom
       CF-hom n (ptd-susp^-fmap m ptd-projr)
       == idhom _
  βr = ! (CF-comp n (ptd-susp^-fmap m ptd-projr)
                    (ptd-susp^-fmap m ptd-winr))
       ∙ ap (CF-hom n)
            (! (ptd-susp^-fmap-∘ m ptd-projr ptd-winr)
             ∙ ap (ptd-susp^-fmap m) ptd-projr-winr
             ∙ ptd-susp^-fmap-idf m _)
       ∙ CF-ident n
    where
    ptd-projr-winr : ptd-projr ∘ptd ptd-winr == ptd-idf _
    ptd-projr-winr = ptd-λ= (λ _ → idp) $
      ∙-unit-r _ ∙ ap-! projr wglue ∙ ap ! Projr.glue-β

  module CSusp^Wedge = ProductRepr
    (CF-hom n (ptd-susp^-fmap m ptd-projl))
    (CF-hom n (ptd-susp^-fmap m ptd-projr))
    (CF-hom n (ptd-susp^-fmap m ptd-winl))
    (CF-hom n (ptd-susp^-fmap m ptd-winr))
    (app= (ap GroupHom.f βl))
    (app= (ap GroupHom.f βr))
    (transport
      (λ {(_ , f , g) → is-exact (CF n g) (CF n f)})
      (suspend^-cof= m ptd-winr ptd-projl
        (pair= CofWinr.ptd-path CofWinr.cfcod-over))
      (C-exact n (ptd-susp^-fmap m ptd-winr)))
    (transport
      (λ {(_ , f , g) → is-exact (CF n g) (CF n f)})
      (suspend^-cof= m ptd-winl ptd-projr
        (pair= CofWinl.ptd-path CofWinl.cfcod-over))
      (C-exact n (ptd-susp^-fmap m ptd-winl)))

  C-susp^-wedge-rec : {Z : Ptd i}
    (winl* : fst X → fst Z) (winr* : fst Y → fst Z)
    (wglue* : winl* (snd X) == winr* (snd Y)) (pt : winl* (snd X) == snd Z)
    → CF-hom n (ptd-susp^-fmap m (WedgeRec.f winl* winr* wglue* , pt))
      == ×-hom (CF-hom n (ptd-susp^-fmap m (winl* , pt)))
               (CF-hom n (ptd-susp^-fmap m (winr* , ! wglue* ∙ pt)))
      [ (λ K → GroupHom (C n (Ptd-Susp^ m Z)) K) ↓ CSusp^Wedge.iso ]
  C-susp^-wedge-rec winl* winr* wglue* pt = codomain-over-iso _ _ _ _ $
    codomain-over-equiv
      (fst (CF n (ptd-susp^-fmap m (WedgeRec.f winl* winr* wglue* , pt)))) _
    ▹ ap2 (λ f g z → (f z , g z))
        (ap GroupHom.f $ ! $
          ap (CF-hom n) (ptd-susp^-fmap-∘ m (rec , pt) ptd-winl)
          ∙ CF-comp n (ptd-susp^-fmap m (rec , pt)) (ptd-susp^-fmap m ptd-winl))
        (ap GroupHom.f $ ! $
          ap (CF-hom n) (ap (ptd-susp^-fmap m) (pair= idp (! pt-lemma))
                         ∙ ptd-susp^-fmap-∘ m (rec , pt) ptd-winr)
          ∙ CF-comp n (ptd-susp^-fmap m (rec , pt)) (ptd-susp^-fmap m ptd-winr))
    where
    rec = WedgeRec.f winl* winr* wglue*

    pt-lemma : ap rec (! wglue) ∙ pt == ! wglue* ∙ pt
    pt-lemma = ap (λ w → w ∙ pt) $
                 ap-! rec wglue ∙ ap ! (WedgeRec.glue-β winl* winr* wglue*)

  C-susp^-wedge-in : {Z : Ptd i}
    (f : fst (Ptd-Susp^ m Z ∙→ Ptd-Susp^ m (Ptd-Wedge X Y)))
    → CF-hom n f
      == ×-sum-hom (C-abelian n _)
           (CF-hom n (ptd-susp^-fmap m ptd-projl ∘ptd f))
           (CF-hom n (ptd-susp^-fmap m ptd-projr ∘ptd f))
      [ (λ G → GroupHom G (C n (Ptd-Susp^ m Z))) ↓ CSusp^Wedge.iso ]
  C-susp^-wedge-in f =
    lemma (C-abelian n _) (C-abelian n _)
          CSusp^Wedge.inl-over CSusp^Wedge.inr-over
    ▹ ap2 (×-sum-hom (C-abelian n _))
        (! (CF-comp n (ptd-susp^-fmap m ptd-projl) f))
        (! (CF-comp n (ptd-susp^-fmap m ptd-projr) f))
    where
    lemma : {G H K L : Group i}
      (aG : is-abelian G) (aL : is-abelian L) {p : G == H ×G K}
      {φ : GroupHom H G} {ψ : GroupHom K G} {χ : GroupHom G L}
      → φ == ×G-inl [ (λ J → GroupHom H J) ↓ p ]
      → ψ == ×G-inr {G = H} [ (λ J → GroupHom K J) ↓ p ]
      → χ == ×-sum-hom aL (χ ∘hom φ) (χ ∘hom ψ) [ (λ J → GroupHom J L) ↓ p ]
    lemma {H = H} {K = K} aG aL {p = idp} {χ = χ} idp idp =
      ap (λ α → χ ∘hom α) (×-sum-hom-η H K aG)
      ∙ ! (∘-×-sum-hom aG aL χ (×G-inl {G = H}) (×G-inr {G = H}))
