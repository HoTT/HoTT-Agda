{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.CofiberSequence
open import cohomology.Exactness
open import cohomology.FunctionOver
open import cohomology.Theory
open import cohomology.ProductRepr
open import cohomology.WedgeCofiber

{- Finite additivity is provable (and in a stronger form) without using
 - the additivity axiom. We have

         Cⁿ(X ∨ Y) == Cⁿ(X) × Cⁿ(Y)

 - and over this path
 -   ∙ Cⁿ(winl) corresponds to fst : Cⁿ(X) × Cⁿ(Y) → Cⁿ(X),
 -   ∙ Cⁿ(winr) corresponds to snd : Cⁿ(X) × Cⁿ(Y) → Cⁿ(Y),
 -   ∙ Cⁿ(Wedge-rec winl* winr* wglue*) : Cⁿ(Z) → Cⁿ(X ∨ Y)
       corresponds to Cⁿ(winl*) × Cⁿ(winr*).
 -   ∙ Cⁿ(f) : Cⁿ(X ∨ Y) → Cⁿ(Z)
       corresponds to Cⁿ(projl ∘ f) + Cⁿ(projr ∘ f) : Cⁿ(X) × Cⁿ(Y) → Cⁿ(Z)
 -}

module cohomology.Wedge {i} (CT : CohomologyTheory i) where

module CWedge (n : ℤ) (X Y : Ptd i) where

  open WedgeCofiber X Y

  open CohomologyTheory CT
  open import cohomology.Functor CT

  private
    βl : CF-hom n ⊙winl ∘ᴳ CF-hom n ⊙projl == idhom _
    βl = ! (CF-comp n ⊙projl ⊙winl) ∙ CF-ident n

    βr : CF-hom n ⊙winr ∘ᴳ CF-hom n ⊙projr == idhom _
    βr = ! (CF-comp n ⊙projr ⊙winr)
         ∙ ap (CF-hom n) ⊙projr-winr
         ∙ CF-ident n
      where
      ⊙projr-winr : ⊙projr ⊙∘ ⊙winr == ⊙idf _
      ⊙projr-winr = ⊙λ= (λ _ → idp) $
        ∙-unit-r _ ∙ ap-! projr wglue ∙ ap ! Projr.glue-β

  open ProductRepr
    (CF-hom n ⊙projl) (CF-hom n ⊙projr)
    (CF-hom n ⊙winl) (CF-hom n ⊙winr)
    (app= (ap GroupHom.f βl)) (app= (ap GroupHom.f βr))
    (transport
      (λ {(_ , g) → is-exact (CF-hom n g) (CF-hom n ⊙winr)})
      (pair= CofWinr.⊙path CofWinr.cfcod-over)
      (C-exact n ⊙winr))
    (transport
      (λ {(_ , g) → is-exact (CF-hom n g) (CF-hom n ⊙winl)})
      (pair= CofWinl.⊙path CofWinl.cfcod-over)
      (C-exact n ⊙winl))
    public

  wedge-rec-over : {Z : Ptd i}
    (winl* : fst X → fst Z) (winr* : fst Y → fst Z)
    (wglue* : winl* (snd X) == winr* (snd Y)) (pt : winl* (snd X) == snd Z)
    → CF-hom n (WedgeRec.f winl* winr* wglue* , pt)
      == ×ᴳ-hom-in (CF-hom n (winl* , pt))
                   (CF-hom n (winr* , ! wglue* ∙ pt))
      [ (λ K → C n Z →ᴳ K) ↓ iso ]
  wedge-rec-over winl* winr* wglue* pt = codomain-over-iso $
    codomain-over-equiv
      (CF n (WedgeRec.f winl* winr* wglue* , pt)) _
    ▹ ap2 (λ f g z → (f z , g z))
        (ap GroupHom.f $ ! $ CF-comp n (rec , pt) ⊙winl)
        (ap GroupHom.f $ ! $
          ap (CF-hom n) (pair= idp (! pt-lemma)) ∙ CF-comp n (rec , pt) ⊙winr)
    where
    rec = WedgeRec.f winl* winr* wglue*

    pt-lemma : ap rec (! wglue) ∙ pt == ! wglue* ∙ pt
    pt-lemma = ap (λ w → w ∙ pt) $
                 ap-! rec wglue ∙ ap ! (WedgeRec.glue-β winl* winr* wglue*)

  wedge-in-over : {Z : Ptd i} (f : fst (Z ⊙→ ⊙Wedge X Y))
    → CF-hom n f
      == ×ᴳ-sum-hom (C-abelian n _) (CF-hom n (⊙projl ⊙∘ f))
                                    (CF-hom n (⊙projr ⊙∘ f))
      [ (λ G → G →ᴳ C n Z) ↓ iso ]
  wedge-in-over f =
    lemma (C-abelian n _) (C-abelian n _) inl-over inr-over
    ▹ ap2 (×ᴳ-sum-hom (C-abelian n _))
        (! (CF-comp n ⊙projl f))
        (! (CF-comp n ⊙projr f))
    where
    lemma : {G H K L : Group i}
      (aG : is-abelian G) (aL : is-abelian L) {p : G == H ×ᴳ K}
      {φ : H →ᴳ G} {ψ : K →ᴳ G} {χ : G →ᴳ L}
      → φ == ×ᴳ-inl [ (λ J → H →ᴳ J) ↓ p ]
      → ψ == ×ᴳ-inr {G = H} [ (λ J → K →ᴳ J) ↓ p ]
      → χ == ×ᴳ-sum-hom aL (χ ∘ᴳ φ) (χ ∘ᴳ ψ) [ (λ J → J →ᴳ L) ↓ p ]
    lemma {H = H} {K = K} aG aL {p = idp} {χ = χ} idp idp =
      ap (λ α → χ ∘ᴳ α) (×ᴳ-sum-hom-η H K aG)
      ∙ ! (∘-×ᴳ-sum-hom aG aL χ (×ᴳ-inl {G = H}) (×ᴳ-inr {G = H}))
