{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import groups.ProductRepr
open import cohomology.Theory
open import homotopy.WedgeCofiber

{- For the cohomology group of a suspension ΣX, the group inverse has the
 - explicit form Cⁿ(flip-susp) : Cⁿ(ΣX) → Cⁿ(ΣX).
 -}

module cohomology.InverseInSusp {i} (CT : CohomologyTheory i)
  (n : ℤ) {X : Ptd i} where

open CohomologyTheory CT
open import cohomology.Wedge CT n (⊙Susp X) (⊙Susp X)

private
  module Subtract = SuspRec {C = de⊙ (⊙Susp X ⊙∨ ⊙Susp X)}
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
      ∙ ! (SuspFlip.merid-β x)

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

  abstract
    cancel : ∀ x
      → GroupHom.f (×ᴳ-fanin (C-is-abelian n _) (C-fmap n (⊙Susp-flip X)) (idhom _)) (x , x)
      == Cident n (⊙Susp X)
    cancel x =
        ap2 (Group.comp (C n (⊙Susp X)))
          (! (CEl-fmap-base-indep n projl-subtract x))
          (! (CEl-fmap-idf n x) ∙ ! (CEl-fmap-base-indep n projr-subtract x))
      ∙ (Wedge-in-comm-sqr' ⊙subtract □$ᴳ (x , x))
      ∙ ap (CEl-fmap n ⊙subtract)
          ( ap (GroupIso.g C-Wedge ∘ diag) (! (CEl-fmap-idf n x))
          ∙ (C-Wedge-rec-comm-sqr' (⊙idf _) (⊙idf _) □$ᴳ x))
      ∙ ∘-CEl-fmap n ⊙subtract ⊙fold x
      ∙ CEl-fmap-base-indep n (λ σ → fold-subtract σ ∙ ! (merid (pt X))) x
      ∙ CEl-fmap-cst n x

abstract
  C-Susp-flip-is-inv : ∀ x → CEl-fmap n (⊙Susp-flip X) x == Group.inv (C n (⊙Susp X)) x
  C-Susp-flip-is-inv x = ! (Group.inv-unique-l (C n (⊙Susp X)) _ x (cancel x))
