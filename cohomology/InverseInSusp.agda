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
open import cohomology.Wedge CT

private
  open WedgeCofiber (⊙Susp X) (⊙Susp X)
  module CW = CWedge n (⊙Susp X) (⊙Susp X)

  module Twice = SuspensionRec (fst X) {C = fst (⊙Susp X ⊙∨ ⊙Susp X)}
    (winl (north _))
    (winl (north _))
    (λ x → ap winl (σloop X x) ∙ wglue ∙ ! (ap winr (σloop X x)) ∙ ! wglue)

  twice = Twice.f

  ⊙twice : fst (⊙Susp X ⊙→ ⊙Susp X ⊙∨ ⊙Susp X)
  ⊙twice = (twice , idp)

  {- Convenience lemma for reducing [ap (f ∘ twice) (merid x)] for some f -}
  ap-on-twice : {A : Type i} (f : fst (⊙Susp X ⊙∨ ⊙Susp X) → A)
    {p : fst X → f (winl (north _)) == f (winl (south _))}
    {q : fst X → f (winr (north _)) == f (winr (south _))}
    {r : f (winl (north _)) == f (winr (north _))}
    → ap (f ∘ winl) ∘ merid _ == p
    → ap (f ∘ winr) ∘ merid _ == q
    → ap f wglue == r
    → ∀ x → ap f (ap twice (merid _ x))
            == (p x ∙ ! (p (snd X))) ∙ r ∙ (q (snd X) ∙ ! (q x)) ∙ ! r
  ap-on-twice f idp idp idp x =
    ap (ap f) (Twice.glue-β x)
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

  ⊙projl-twice : ⊙projl ⊙∘ ⊙twice == ⊙idf (⊙Susp X)
  ⊙projl-twice = ⊙λ=
    (Suspension-elim (fst X) idp (merid _ (snd X)) $
      ↓-∘=idf-from-square projl twice ∘ λ x →
        (ap-on-twice projl
           (λ= (ap-idf ∘ merid _)) (λ= (ap-cst _ ∘ merid _)) Projl.glue-β x
         ∙ ∙-unit-r _)
        ∙v⊡ square-lemma (merid _ x) (merid _ (snd X)))
    idp
    where
    square-lemma : {A : Type i} {x y z : A} (p : x == y) (q : z == y)
      → Square idp (p ∙ ! q) p q
    square-lemma idp idp = ids

  ⊙projr-twice : ⊙projr ⊙∘ ⊙twice == ⊙flip-susp X
  ⊙projr-twice = ⊙λ=
    (Suspension-elim (fst X) (merid _ (snd X)) idp $
      ↓-='-from-square ∘ λ x →
        (ap-∘ projr twice (merid _ x)
         ∙ ap-on-twice projr
             (λ= (ap-cst _ ∘ merid _)) (λ= (ap-idf ∘ merid _)) Projr.glue-β x
         ∙ ∙-unit-r _)
        ∙v⊡ square-lemma (merid _ x) (merid _ (snd X))
        ⊡v∙ ! (FlipSusp.glue-β x))
    (! (!-inv-r (merid _ (snd X))))
    where
    square-lemma : {A : Type i} {x y z : A} (p : x == y) (q : z == y)
      → Square q (q ∙ ! p) (! p) idp
    square-lemma idp idp = ids

  ⊙fold-twice : ⊙fold ⊙∘ ⊙twice == ⊙cst
  ⊙fold-twice = ⊙λ=
    (Suspension-elim (fst X) idp idp $
      ↓-='-in ∘ ! ∘ λ x →
        ap-∘ fold twice (merid _ x)
        ∙ ap-on-twice fold
            (λ= (ap-idf ∘ merid _)) (λ= (ap-idf ∘ merid _)) Fold.glue-β x
        ∙ lemma (merid _ x) (merid _ (snd X))
        ∙ ! (ap-cst (north _) (glue x)))
    idp
    where
    lemma : {A : Type i} {x y z : A} (p : x == y) (q : z == y)
      → (p ∙ ! q) ∙ (q ∙ ! p) ∙ idp == idp
    lemma idp idp = idp

  cancel :
    ×ᴳ-sum-hom (C-abelian n _) (idhom _) (CF-hom n (⊙flip-susp X)) ∘ᴳ ×ᴳ-diag
    == cst-hom
  cancel =
    ap2 (λ φ ψ → ×ᴳ-sum-hom (C-abelian n _) φ ψ ∘ᴳ ×ᴳ-diag)
        (! (CF-ident n) ∙ ap (CF-hom n) (! ⊙projl-twice))
        (ap (CF-hom n) (! ⊙projr-twice))
    ∙ transport (λ {(G , φ , ψ) → φ ∘ᴳ ψ == cst-hom})
        (pair= (CW.iso) $ ↓-×-in
          (CW.wedge-in-over ⊙twice)
          (CW.wedge-rec-over (idf _) (idf _) idp idp
           ▹ ap2 ×ᴳ-hom-in (CF-ident n) (CF-ident n)))
        (! (CF-comp n ⊙fold ⊙twice) ∙ ap (CF-hom n) ⊙fold-twice ∙ CF-cst n)

C-flip-susp-is-inv :
  CF-hom n (⊙flip-susp X) == inv-hom (C n (⊙Susp X)) (C-abelian _ _)
C-flip-susp-is-inv = hom= _ _ $ λ= $ λ g →
  ! (group-inv-unique-r (C n (⊙Susp X)) g _ (app= (ap GroupHom.f cancel) g))
