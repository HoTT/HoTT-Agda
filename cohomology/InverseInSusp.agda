{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.FunctionOver
open import cohomology.ProductRepr
open import cohomology.Theory
open import cohomology.WedgeCofiber

{- For the cohomology group of a suspension ΣX, the group inverse has the
   explicit form Cⁿ(flip-susp) : Cⁿ(ΣX) → Cⁿ(ΣX).

-}

module cohomology.InverseInSusp {i} (CT : CohomologyTheory i)
  (n : ℤ) {X : Ptd i} where

open CohomologyTheory CT
open import cohomology.Functor CT
open import cohomology.BaseIndependence CT
open import cohomology.Wedge CT

private
  open WedgeCofiber (⊙Susp X) (⊙Susp X)
  module CW = CWedge n (⊙Susp X) (⊙Susp X)

  module Subtract = SuspensionRec (fst X) {C = fst (⊙Susp X ⊙∨ ⊙Susp X)}
    (winl (north _))
    (winl (north _))
    (λ x → ap winl (σloop X x) ∙ wglue ∙ ! (ap winr (σloop X x)) ∙ ! wglue)

  subtract = Subtract.f

  ⊙subtract : fst (⊙Susp X ⊙→ ⊙Susp X ⊙∨ ⊙Susp X)
  ⊙subtract = (subtract , idp)

  {- Convenience lemma for reducing [ap (f ∘ subtract) (merid x)] for some f -}
  ap-on-subtract : {A : Type i} (f : fst (⊙Susp X ⊙∨ ⊙Susp X) → A)
    {p : fst X → f (winl (north _)) == f (winl (south _))}
    {q : fst X → f (winr (north _)) == f (winr (south _))}
    {r : f (winl (north _)) == f (winr (north _))}
    → ap (f ∘ winl) ∘ merid _ == p
    → ap (f ∘ winr) ∘ merid _ == q
    → ap f wglue == r
    → ∀ x → ap f (ap subtract (merid _ x))
            == (p x ∙ ! (p (snd X))) ∙ r ∙ (q (snd X) ∙ ! (q x)) ∙ ! r
  ap-on-subtract f idp idp idp x =
    ap (ap f) (Subtract.glue-β x)
    ∙ lemma f winl winr (merid _ x) (merid _ (snd X)) wglue wglue
    where
    lemma : {A B C : Type i} (g : B → C) (f₁ f₂ : A → B)
      {x y z : A}
      (p : x == y) (q : z == y) (r : f₁ z == f₂ z) (s : f₁ x == f₂ x)
      → ap g (ap f₁ (p ∙ ! q) ∙ r ∙ ! (ap f₂ (p ∙ ! q)) ∙ ! s)
        == (ap (g ∘ f₁) p ∙ ! (ap (g ∘ f₁) q)) ∙ ap g r
           ∙ (ap (g ∘ f₂) q ∙ ! (ap (g ∘ f₂) p)) ∙ ! (ap g s)
    lemma g f₁ f₂ idp idp r s =
      ap-∙ g r (! s) ∙ ap (λ w → ap g r ∙ w) (ap-! g s)

  projl-subtract : ∀ σ → projl _ _ (subtract σ) == σ
  projl-subtract = Suspension-elim (fst X) idp (merid _ (snd X)) $
    ↓-∘=idf-from-square (projl _ _) subtract ∘ λ x →
      (ap-on-subtract (projl _ _)
         (λ= (ap-idf ∘ merid _))
         (λ= (ap-cst _ ∘ merid _)) (Projl.glue-β _ _) x
       ∙ ∙-unit-r _)
      ∙v⊡ square-lemma (merid _ x) (merid _ (snd X))
    where
    square-lemma : {A : Type i} {x y z : A} (p : x == y) (q : z == y)
      → Square idp (p ∙ ! q) p q
    square-lemma idp idp = ids

  projr-subtract : ∀ σ → projr _ _ (subtract σ) == flip-susp σ
  projr-subtract = Suspension-elim (fst X) (merid _ (snd X)) idp $
    ↓-='-from-square ∘ λ x →
      (ap-∘ (projr _ _) subtract (merid _ x)
       ∙ ap-on-subtract (projr _ _)
           (λ= (ap-cst _ ∘ merid _))
           (λ= (ap-idf ∘ merid _)) (Projr.glue-β _ _) x
       ∙ ∙-unit-r _)
      ∙v⊡ square-lemma (merid _ x) (merid _ (snd X))
      ⊡v∙ ! (FlipSusp.glue-β x)
    where
    square-lemma : {A : Type i} {x y z : A} (p : x == y) (q : z == y)
      → Square q (q ∙ ! p) (! p) idp
    square-lemma idp idp = ids

  fold-subtract : ∀ σ → fold (subtract σ) == north _
  fold-subtract = Suspension-elim (fst X) idp idp $
    ↓-='-in ∘ ! ∘ λ x →
      ap-∘ fold subtract (merid _ x)
      ∙ ap-on-subtract fold
          (λ= (ap-idf ∘ merid _)) (λ= (ap-idf ∘ merid _)) Fold.glue-β x
      ∙ lemma (merid _ x) (merid _ (snd X))
      ∙ ! (ap-cst (north _) (glue x))
    where
    lemma : {A : Type i} {x y z : A} (p : x == y) (q : z == y)
      → (p ∙ ! q) ∙ (q ∙ ! p) ∙ idp == idp
    lemma idp idp = idp

  cancel :
    ×ᴳ-sum-hom (C-abelian n _) (idhom _) (CF-hom n (⊙flip-susp X)) ∘ᴳ ×ᴳ-diag
    == cst-hom
  cancel =
    ap2 (λ φ ψ → ×ᴳ-sum-hom (C-abelian n _) φ ψ ∘ᴳ ×ᴳ-diag)
        (! (CF-ident n) ∙ ! (CF-λ= n projl-subtract))
        (! (CF-λ= n projr-subtract))
    ∙ transport (λ {(G , φ , ψ) → φ ∘ᴳ ψ == cst-hom})
        (pair= (CW.path) $ ↓-×-in
          (CW.wedge-in-over ⊙subtract)
          (CW.⊙wedge-rec-over (⊙idf _) (⊙idf _)
           ▹ ap2 ×ᴳ-hom-in (CF-ident n) (CF-ident n)))
        (! (CF-comp n ⊙fold ⊙subtract) ∙ CF-λ= n fold-subtract ∙ CF-cst n)

C-flip-susp-is-inv :
  CF-hom n (⊙flip-susp X) == inv-hom (C n (⊙Susp X)) (C-abelian _ _)
C-flip-susp-is-inv = hom= _ _ $ λ= $ λ g →
  ! (group-inv-unique-r (C n (⊙Susp X)) g _ (app= (ap GroupHom.f cancel) g))
