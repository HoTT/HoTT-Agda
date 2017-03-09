{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import groups.Exactness
open import homotopy.CofiberSequence
open import cohomology.Theory

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

module cohomology.Wedge {i} (CT : CohomologyTheory i)
  (n : ℤ) (X Y : Ptd i) where

  open import homotopy.WedgeCofiber X Y

  open CohomologyTheory CT
  open import cohomology.Functor CT
  open import cohomology.PtdMapSequence CT

  private
    abstract
      βl : ∀ x → CEl-fmap n ⊙winl (CEl-fmap n (⊙projl X Y) x) == x
      βl = CEl-fmap-inverse n ⊙winl (⊙projl X Y) λ _ → idp

      βr : ∀ y → CEl-fmap n ⊙winr (CEl-fmap n (⊙projr X Y) y) == y
      βr = CEl-fmap-inverse n ⊙winr (⊙projr X Y) λ _ → idp

      C-projr-C-winl-is-exact : is-exact (C-fmap n (⊙projr X Y)) (C-fmap n ⊙winl)
      C-projr-C-winl-is-exact = equiv-preserves'-exact
        (C-comm-square n cfcod-winl-projr-comm-sqr)
        (C-comm-square n $ comm-sqr λ _ → idp)
        (snd (C-emap n CofWinl.⊙eq))
        (C-isemap n (⊙idf _) (idf-is-equiv _))
        (C-isemap n (⊙idf _) (idf-is-equiv _))
        (C-exact n ⊙winl)

      C-projl-C-winr-is-exact : is-exact (C-fmap n (⊙projl X Y)) (C-fmap n ⊙winr)
      C-projl-C-winr-is-exact = equiv-preserves'-exact
        (C-comm-square n cfcod-winr-projl-comm-sqr)
        (C-comm-square n $ comm-sqr λ _ → idp)
        (snd (C-emap n CofWinr.⊙eq))
        (C-isemap n (⊙idf _) (idf-is-equiv _))
        (C-isemap n (⊙idf _) (idf-is-equiv _))
        (C-exact n ⊙winr)

  import groups.ProductRepr
    (C-fmap n (⊙projl X Y)) (C-fmap n (⊙projr X Y))
    (C-fmap n ⊙winl) (C-fmap n ⊙winr) βl βr
    C-projl-C-winr-is-exact
    C-projr-C-winl-is-exact as PR

  C-Wedge = PR.iso

{-
  ⊙Wedge-rec-over : {Z : Ptd i} (winl* : X ⊙→ Z) (winr* : Y ⊙→ Z)
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
    → φ == ×ᴳ-fanin (C-is-abelian n _) (φ ∘ᴳ CF-hom n (⊙projl X Y))
                                       (φ ∘ᴳ CF-hom n (⊙projr X Y))
      [ (λ G → G →ᴳ C n Z) ↓ path ]
  Wedge-hom-η φ =
    lemma (C-is-abelian n _) (C-is-abelian n _) inl-over inr-over
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

  Wedge-in-over : {Z : Ptd i} (f : Z ⊙→ ⊙Wedge X Y)
    → CF-hom n f
      == ×ᴳ-fanin (C-is-abelian n _) (CF-hom n (⊙projl X Y ⊙∘ f))
                                     (CF-hom n (⊙projr X Y ⊙∘ f))
      [ (λ G → G →ᴳ C n Z) ↓ path ]
  Wedge-in-over f =
    Wedge-hom-η (CF-hom n f)
    ▹ ap2 (×ᴳ-fanin (C-is-abelian n _))
        (! (CF-comp n (⊙projl X Y) f))
        (! (CF-comp n (⊙projr X Y) f))
-}
