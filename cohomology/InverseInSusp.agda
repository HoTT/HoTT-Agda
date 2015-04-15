{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.FunctionOver
open import cohomology.ProductRepr
open import cohomology.Theory
open import cohomology.WedgeCofiber

{- For the cohomology group of a suspension ΣX, the group inverse has the
 - explicit form Cⁿ(flip-susp) : Cⁿ(ΣX) → Cⁿ(ΣX).
 -}

module cohomology.InverseInSusp {i} (CT : CohomologyTheory i)
  (n : ℤ) {X : Ptd i} where

open CohomologyTheory CT
open import cohomology.Functor CT
open import cohomology.BaseIndependence CT
open import cohomology.Wedge CT

private
  module CW = CWedge n (⊙Susp X) (⊙Susp X)

  module Subtract = SuspensionRec (fst X) {C = fst (⊙Susp X ⊙∨ ⊙Susp X)}
    (winl (south _))
    (winr (south _))
    (λ x → ap winl (! (merid _ x)) ∙ wglue ∙ ap winr (merid _ x))

  subtract = Subtract.f

  ⊙subtract : fst (⊙Susp X ⊙→ ⊙Susp X ⊙∨ ⊙Susp X)
  ⊙subtract = (subtract , ! (ap winl (merid _ (snd X))))

  projl-subtract : ∀ σ → projl _ _ (subtract σ) == flip-susp σ
  projl-subtract = Suspension-elim (fst X) idp idp $
    ↓-='-from-square ∘ vert-degen-square ∘ λ x →
      ap-∘ (projl _ _) subtract (merid _ x)
      ∙ ap (ap (projl _ _)) (Subtract.glue-β x)
      ∙ ap-∙ (projl _ _) (ap winl (! (merid _ x))) (wglue ∙ ap winr (merid _ x))
      ∙ ((∘-ap (projl _ _) winl (! (merid _ x))
          ∙ ap-idf _)
         ∙2 (ap-∙ (projl _ _) wglue (ap winr (merid _ x))
             ∙ (Projl.glue-β _ _
                ∙2 (∘-ap (projl _ _) winr (merid _ x) ∙ ap-cst _ _))))
      ∙ ∙-unit-r _
      ∙ ! (FlipSusp.glue-β x)

  projr-subtract : ∀ σ → projr _ _ (subtract σ) == σ
  projr-subtract = Suspension-elim (fst X) idp idp $
    ↓-∘=idf-in (projr _ _) subtract ∘ λ x →
      ap (ap (projr _ _)) (Subtract.glue-β x)
      ∙ ap-∙ (projr _ _) (ap winl (! (merid _ x))) (wglue ∙ ap winr (merid _ x))
      ∙ ((∘-ap (projr _ _) winl (! (merid _ x)) ∙ ap-cst _ _)
         ∙2 (ap-∙ (projr _ _) wglue (ap winr (merid _ x))
             ∙ (Projr.glue-β _ _
                ∙2 (∘-ap (projr _ _) winr (merid _ x) ∙ ap-idf _))))

  fold-subtract : ∀ σ → fold (subtract σ) == south _
  fold-subtract = Suspension-elim (fst X) idp idp $
    ↓-app=cst-in ∘ ! ∘ λ x →
      ∙-unit-r _
      ∙ ap-∘ fold subtract (merid _ x)
      ∙ ap (ap fold) (Subtract.glue-β x)
      ∙ ap-∙ fold (ap winl (! (merid _ x))) (wglue ∙ ap winr (merid _ x))
      ∙ ((∘-ap fold winl (! (merid _ x)) ∙ ap-idf _)
         ∙2 (ap-∙ fold wglue (ap winr (merid _ x))
             ∙ (Fold.glue-β
                ∙2 (∘-ap fold winr (merid _ x) ∙ ap-idf _))))
      ∙ !-inv-l (merid _ x)

  cancel :
    ×ᴳ-sum-hom (C-abelian n _) (CF-hom n (⊙flip-susp X)) (idhom _) ∘ᴳ ×ᴳ-diag
    == cst-hom
  cancel =
    ap2 (λ φ ψ → ×ᴳ-sum-hom (C-abelian n _) φ ψ ∘ᴳ ×ᴳ-diag)
        (! (CF-λ= n projl-subtract))
        (! (CF-ident n) ∙ ! (CF-λ= n projr-subtract))
    ∙ transport (λ {(G , φ , ψ) → φ ∘ᴳ ψ == cst-hom})
        (pair= (CW.path) $ ↓-×-in
          (CW.wedge-in-over ⊙subtract)
          (CW.⊙wedge-rec-over (⊙idf _) (⊙idf _)
           ▹ ap2 ×ᴳ-hom-in (CF-ident n) (CF-ident n)))
        (! (CF-comp n ⊙fold ⊙subtract)
         ∙ CF-λ= n (λ σ → fold-subtract σ ∙ ! (merid _ (snd X)))
         ∙ CF-cst n)

C-flip-susp-is-inv :
  CF-hom n (⊙flip-susp X) == inv-hom (C n (⊙Susp X)) (C-abelian _ _)
C-flip-susp-is-inv = hom= _ _ $ λ= $ λ g →
  ! (group-inv-unique-l (C n (⊙Susp X)) _ g (app= (ap GroupHom.f cancel) g))
