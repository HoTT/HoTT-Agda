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
    βl : CF-hom n ⊙winl ∘ᴳ CF-hom n (⊙projl X Y) == idhom _
    βl = ! (CF-comp n (⊙projl X Y) ⊙winl) ∙ CF-ident n

    βr : CF-hom n ⊙winr ∘ᴳ CF-hom n (⊙projr X Y) == idhom _
    βr = ! (CF-comp n (⊙projr X Y) ⊙winr)
         ∙ ap (CF-hom n) ⊙projr-winr
         ∙ CF-ident n
      where
      ⊙projr-winr : ⊙projr X Y ⊙∘ ⊙winr == ⊙idf _
      ⊙projr-winr = ⊙λ= (λ _ → idp) $
        ∙-unit-r _ ∙ ap-! (projr X Y) wglue ∙ ap ! (Projr.glue-β X Y)

  open ProductRepr
    (CF-hom n (⊙projl X Y)) (CF-hom n (⊙projr X Y))
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

  ⊙Wedge-rec-over : {Z : Ptd i} (winl* : fst (X ⊙→ Z)) (winr* : fst (Y ⊙→ Z))
    → CF-hom n (⊙Wedge-rec winl* winr*)
      == ×ᴳ-fanout (CF-hom n winl*) (CF-hom n (winr*))
      [ (λ K → C n Z →ᴳ K) ↓ path ]
  ⊙Wedge-rec-over winl* winr* = codomain-over-iso $
    codomain-over-equiv (CF n R.⊙f) _
    ▹ ap2 (λ f g z → (f z , g z))
          (ap GroupHom.f $ ! (CF-comp n R.⊙f ⊙winl) ∙ ap (CF-hom n) R.⊙winl-β)
          (ap GroupHom.f $ ! (CF-comp n R.⊙f ⊙winr) ∙ ap (CF-hom n) R.⊙winr-β)
    where
    module R = ⊙WedgeRec winl* winr*

  Wedge-hom-η : {Z : Ptd i} (φ : C n (⊙Wedge X Y) →ᴳ C n Z)
    → φ == ×ᴳ-fanin (C-abelian n _) (φ ∘ᴳ CF-hom n (⊙projl X Y))
                                    (φ ∘ᴳ CF-hom n (⊙projr X Y))
      [ (λ G → G →ᴳ C n Z) ↓ path ]
  Wedge-hom-η φ =
    lemma (C-abelian n _) (C-abelian n _) inl-over inr-over
    where
    lemma : {G H K L : Group i}
      (aG : is-abelian G) (aL : is-abelian L) {p : G == H ×ᴳ K}
      {φ : H →ᴳ G} {ψ : K →ᴳ G} {χ : G →ᴳ L}
      → φ == ×ᴳ-inl [ (λ J → H →ᴳ J) ↓ p ]
      → ψ == ×ᴳ-inr {G = H} [ (λ J → K →ᴳ J) ↓ p ]
      → χ == ×ᴳ-fanin aL (χ ∘ᴳ φ) (χ ∘ᴳ ψ) [ (λ J → J →ᴳ L) ↓ p ]
    lemma {H = H} {K = K} aG aL {p = idp} {χ = χ} idp idp =
      ap (λ α → χ ∘ᴳ α) (×ᴳ-fanin-η H K aG)
      ∙ ! (×ᴳ-fanin-pre∘ aG aL χ (×ᴳ-inl {G = H}) (×ᴳ-inr {G = H}))

  Wedge-in-over : {Z : Ptd i} (f : fst (Z ⊙→ ⊙Wedge X Y))
    → CF-hom n f
      == ×ᴳ-fanin (C-abelian n _) (CF-hom n (⊙projl X Y ⊙∘ f))
                                    (CF-hom n (⊙projr X Y ⊙∘ f))
      [ (λ G → G →ᴳ C n Z) ↓ path ]
  Wedge-in-over f =
    Wedge-hom-η (CF-hom n f)
    ▹ ap2 (×ᴳ-fanin (C-abelian n _))
        (! (CF-comp n (⊙projl X Y) f))
        (! (CF-comp n (⊙projr X Y) f))
