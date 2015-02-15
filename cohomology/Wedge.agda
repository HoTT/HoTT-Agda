{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.CofiberSequence
open import cohomology.Exactness
open import cohomology.FunctionOver
open import cohomology.Theory
open import cohomology.ProductRepr
open import cohomology.WedgeCofiber

{- Finite additivity is provable (and in a stronger form) without using
 - the additivity axiom. For any m ≥ 0,

         Cⁿ(Σᵐ(X ∨ Y)) == Cⁿ(ΣᵐX) × Cⁿ(ΣᵐY)

 - and over this path
\ -   ∙ Cⁿ(Σᵐwinl) corresponds to fst : Cⁿ(ΣᵐX) × Cⁿ(ΣᵐY) → Cⁿ(ΣᵐX),
 -   ∙ Cⁿ(Σᵐwinr) corresponds to snd : Cⁿ(ΣᵐX) × Cⁿ(ΣᵐY) → Cⁿ(ΣᵐY),
 -   ∙ Cⁿ(Σᵐ(Wedge-rec winl* winr* wglue*)) : Cⁿ(ΣᵐZ) → Cⁿ(Σᵐ(X ∨ Y))
       corresponds to Cⁿ(Σᵐwinl*) × Cⁿ(Σᵐwinr*).
 -}

module cohomology.Wedge {i} (CT : CohomologyTheory i) where

module CSusp^Wedge (n : ℤ) (X Y : Ptd i) (m : ℕ) where

  open WedgeCofiber X Y

  open CohomologyTheory CT
  open import cohomology.ConstantFunction CT

  private
    βl : CF-hom n (⊙susp^-fmap m ⊙winl) ∘ᴳ
         CF-hom n (⊙susp^-fmap m ⊙projl)
         == idhom _
    βl = ! (CF-comp n (⊙susp^-fmap m ⊙projl)
                       (⊙susp^-fmap m ⊙winl))
         ∙ ap (CF-hom n)
              (! (⊙susp^-fmap-∘ m ⊙projl ⊙winl)
               ∙ ⊙susp^-fmap-idf m _)
         ∙ CF-ident n

    βr : CF-hom n (⊙susp^-fmap m ⊙winr) ∘ᴳ
         CF-hom n (⊙susp^-fmap m ⊙projr)
         == idhom _
    βr = ! (CF-comp n (⊙susp^-fmap m ⊙projr)
                      (⊙susp^-fmap m ⊙winr))
         ∙ ap (CF-hom n)
              (! (⊙susp^-fmap-∘ m ⊙projr ⊙winr)
               ∙ ap (⊙susp^-fmap m) ⊙projr-winr
               ∙ ⊙susp^-fmap-idf m _)
         ∙ CF-ident n
      where
      ⊙projr-winr : ⊙projr ⊙∘ ⊙winr == ⊙idf _
      ⊙projr-winr = ⊙λ= (λ _ → idp) $
        ∙-unit-r _ ∙ ap-! projr wglue ∙ ap ! Projr.glue-β

  open ProductRepr
    (CF-hom n (⊙susp^-fmap m ⊙projl))
    (CF-hom n (⊙susp^-fmap m ⊙projr))
    (CF-hom n (⊙susp^-fmap m ⊙winl))
    (CF-hom n (⊙susp^-fmap m ⊙winr))
    (app= (ap GroupHom.f βl))
    (app= (ap GroupHom.f βr))
    (transport
      (λ {(_ , f , g) → is-exact (CF n g) (CF n f)})
      (suspend^-cof= m ⊙winr ⊙projl
        (pair= CofWinr.⊙path CofWinr.cfcod-over))
      (C-exact n (⊙susp^-fmap m ⊙winr)))
    (transport
      (λ {(_ , f , g) → is-exact (CF n g) (CF n f)})
      (suspend^-cof= m ⊙winl ⊙projr
        (pair= CofWinl.⊙path CofWinl.cfcod-over))
      (C-exact n (⊙susp^-fmap m ⊙winl)))
    public

  wedge-rec-over : {Z : Ptd i}
    (winl* : fst X → fst Z) (winr* : fst Y → fst Z)
    (wglue* : winl* (snd X) == winr* (snd Y)) (pt : winl* (snd X) == snd Z)
    → CF-hom n (⊙susp^-fmap m (WedgeRec.f winl* winr* wglue* , pt))
      == ×ᴳ-hom-in (CF-hom n (⊙susp^-fmap m (winl* , pt)))
                   (CF-hom n (⊙susp^-fmap m (winr* , ! wglue* ∙ pt)))
      [ (λ K → C n (⊙Susp^ m Z) →ᴳ K) ↓ iso ]
  wedge-rec-over winl* winr* wglue* pt = codomain-over-iso _ _ _ _ $
    codomain-over-equiv
      (fst (CF n (⊙susp^-fmap m (WedgeRec.f winl* winr* wglue* , pt)))) _
    ▹ ap2 (λ f g z → (f z , g z))
        (ap GroupHom.f $ ! $
          ap (CF-hom n) (⊙susp^-fmap-∘ m (rec , pt) ⊙winl)
          ∙ CF-comp n (⊙susp^-fmap m (rec , pt)) (⊙susp^-fmap m ⊙winl))
        (ap GroupHom.f $ ! $
          ap (CF-hom n) (ap (⊙susp^-fmap m) (pair= idp (! pt-lemma))
                         ∙ ⊙susp^-fmap-∘ m (rec , pt) ⊙winr)
          ∙ CF-comp n (⊙susp^-fmap m (rec , pt)) (⊙susp^-fmap m ⊙winr))
    where
    rec = WedgeRec.f winl* winr* wglue*

    pt-lemma : ap rec (! wglue) ∙ pt == ! wglue* ∙ pt
    pt-lemma = ap (λ w → w ∙ pt) $
                 ap-! rec wglue ∙ ap ! (WedgeRec.glue-β winl* winr* wglue*)

  wedge-in-over : {Z : Ptd i}
    (f : fst (⊙Susp^ m Z ⊙→ ⊙Susp^ m (⊙Wedge X Y)))
    → CF-hom n f
      == ×ᴳ-sum-hom (C-abelian n _)
           (CF-hom n (⊙susp^-fmap m ⊙projl ⊙∘ f))
           (CF-hom n (⊙susp^-fmap m ⊙projr ⊙∘ f))
      [ (λ G → G →ᴳ C n (⊙Susp^ m Z)) ↓ iso ]
  wedge-in-over f =
    lemma (C-abelian n _) (C-abelian n _) inl-over inr-over
    ▹ ap2 (×ᴳ-sum-hom (C-abelian n _))
        (! (CF-comp n (⊙susp^-fmap m ⊙projl) f))
        (! (CF-comp n (⊙susp^-fmap m ⊙projr) f))
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
