{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.FunctionOver
open import groups.ProductRepr
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

  module Subtract = SuspRec {C = fst (⊙Susp X ⊙∨ ⊙Susp X)}
    (winl south)
    (winr south)
    (λ x → ap winl (! (merid x)) ∙ wglue ∙ ap winr (merid x))

  subtract = Subtract.f

  ⊙subtract : ⊙Susp X ⊙→ ⊙Susp X ⊙∨ ⊙Susp X
  ⊙subtract = (subtract , ! (ap winl (merid (pt X))))

  projl-subtract : ∀ σ → projl _ _ (subtract σ) == Susp-flip σ
  projl-subtract = Susp-elim idp idp $
    ↓-='-from-square ∘ vert-degen-square ∘ λ x →
      ap-∘ (projl _ _) subtract (merid x)
      ∙ ap (ap (projl _ _)) (Subtract.merid-β x)
      ∙ ap-∙ (projl _ _) (ap winl (! (merid x))) (wglue ∙ ap winr (merid x))
      ∙ ((∘-ap (projl _ _) winl (! (merid x))
          ∙ ap-idf _)
         ∙2 (ap-∙ (projl _ _) wglue (ap winr (merid x))
             ∙ (Projl.glue-β _ _
                ∙2 (∘-ap (projl _ _) winr (merid x) ∙ ap-cst _ _))))
      ∙ ∙-unit-r _
      ∙ ! (FlipSusp.merid-β x)

  projr-subtract : ∀ σ → projr _ _ (subtract σ) == σ
  projr-subtract = Susp-elim idp idp $
    ↓-∘=idf-in' (projr _ _) subtract ∘ λ x →
      ap (ap (projr _ _)) (Subtract.merid-β x)
      ∙ ap-∙ (projr _ _) (ap winl (! (merid x))) (wglue ∙ ap winr (merid x))
      ∙ ((∘-ap (projr _ _) winl (! (merid x)) ∙ ap-cst _ _)
         ∙2 (ap-∙ (projr _ _) wglue (ap winr (merid x))
             ∙ (Projr.glue-β _ _
                ∙2 (∘-ap (projr _ _) winr (merid x) ∙ ap-idf _))))

  fold-subtract : ∀ σ → fold (subtract σ) == south
  fold-subtract = Susp-elim idp idp $
    ↓-app=cst-in ∘ ! ∘ λ x →
      ∙-unit-r _
      ∙ ap-∘ fold subtract (merid x)
      ∙ ap (ap fold) (Subtract.merid-β x)
      ∙ ap-∙ fold (ap winl (! (merid x))) (wglue ∙ ap winr (merid x))
      ∙ ((∘-ap fold winl (! (merid x)) ∙ ap-idf _)
         ∙2 (ap-∙ fold wglue (ap winr (merid x))
             ∙ (Fold.glue-β
                ∙2 (∘-ap fold winr (merid x) ∙ ap-idf _))))
      ∙ !-inv-l (merid x)

  cancel :
    ×ᴳ-fanin (C-is-abelian n _) (CF-hom n (⊙Susp-flip X)) (idhom _) ∘ᴳ ×ᴳ-diag
    == cst-hom
  cancel =
    ap2 (λ φ ψ → ×ᴳ-fanin (C-is-abelian n _) φ ψ ∘ᴳ ×ᴳ-diag)
        (! (CF-λ= n projl-subtract))
        (! (CF-ident n) ∙ ! (CF-λ= n projr-subtract))
    ∙ transport (λ {(G , φ , ψ) → φ ∘ᴳ ψ == cst-hom})
        (pair= (CW.path) $ ↓-×-in
          (CW.Wedge-in-over ⊙subtract)
          (CW.⊙Wedge-rec-over (⊙idf _) (⊙idf _)
           ▹ ap2 ×ᴳ-fanout (CF-ident n) (CF-ident n)))
        (! (CF-comp n ⊙fold ⊙subtract)
         ∙ CF-λ= n (λ σ → fold-subtract σ ∙ ! (merid (pt X)))
         ∙ CF-cst n)

C-Susp-flip-is-inv :
  CF-hom n (⊙Susp-flip X) == inv-hom (C n (⊙Susp X)) (C-is-abelian _ _)
C-Susp-flip-is-inv = group-hom= $ λ= λ g →
  ! (Group.inv-unique-l (C n (⊙Susp X)) _ g (app= (ap GroupHom.f cancel) g))
