{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.FunctionOver
open import cohomology.ProductRepr
open import cohomology.OrdinaryTheory
open import cohomology.WedgeCofiber

{- For the cohomology group of a suspension ΣX, the group inverse has the
   explicit form Cₙ(flip-susp) : Cₙ(ΣX) → Cₙ(ΣX). The proof is via the
   hexagon lemma, with the diagram

                Cₙ(X)
                  |
                fold*
         winl*    ↓    winr*
   Cₙ(X) ←–––– Cₙ(X∨X) ––––→ Cₙ(X)
                  |
                diff*
                  ↓
                Cₙ(X)

-}

module cohomology.InverseInSusp {i} (OT : OrdinaryTheory i) (n : ℤ) {X : Ptd i}
  where

open OrdinaryTheory OT
open import cohomology.ConstantFunction OT
open import cohomology.Wedge OT

private
  open WedgeCofiber X X
  open CSusp^Wedge n X X 1

  module Diff = SuspensionRec (fst X)
    (north (Wedge X X)) (north (Wedge X X))
    (λ x → merid _ (winl x) ∙ ! (merid _ (winr x)))

  diff = Diff.f

  ptd-diff : fst (Ptd-Susp X ∙→ Ptd-Susp (Ptd-Wedge X X))
  ptd-diff = (diff , idp)

  module HL = HexagonLemma
    (CF-hom n (ptd-susp-fmap ptd-fold))
    (CF-hom n ptd-diff)
    (app= $ ap GroupHom.f $
      ! (CF-comp n (ptd-susp-fmap ptd-fold) ptd-diff)
      ∙ ap (CF-hom n)
           (ptd-λ= (Suspension-elim _ idp idp
                     (λ x → ↓-app=cst-from-square $ vert-degen-square $
                       ap-∘ (susp-fmap fold) diff (merid _ x)
                       ∙ ap (ap (susp-fmap fold)) (Diff.glue-β x)
                       ∙ ap-∙ (susp-fmap fold) (merid _ (winl x))
                                               (! (merid _ (winr x)))
                       ∙ ap2 _∙_ (SuspFmap.glue-β fold (winl x))
                                 (ap-! (susp-fmap fold) (merid _ (winr x))
                                  ∙ ap ! (SuspFmap.glue-β fold (winr x)))
                       ∙ !-inv-r (merid _ x)))
                   idp)
      ∙ CF-cst n)

CF-flip : CF-hom n (ptd-flip-susp X) == inv-hom _ (C-abelian n (Ptd-Susp X))
CF-flip =
  ! C-right-reduce
  ∙ (hom= _ _ $ λ= $ ! ∘ HL.inv₁)
  ∙ ap (λ φ → inv-hom _ (C-abelian n (Ptd-Susp X)) ∘hom φ) C-left-reduce
  where
  {- Lemmas are all just reducing compositions -}

  β : {A B C D : Type i} (h : C → D) (g : B → C) (f : A → B) (a : A)
    → ap (susp-fmap h ∘ susp-fmap g ∘ susp-fmap f) (merid _ a)
      == merid _ (h (g (f a)))
  β h g f a =
      ap-∘ (susp-fmap h ∘ susp-fmap g) (susp-fmap f) (merid _ a)
    ∙ ap (ap (susp-fmap h ∘ susp-fmap g)) (SuspFmap.glue-β f a)
    ∙ ap-∘ (susp-fmap h) (susp-fmap g) (merid _ (f a))
    ∙ ap (ap (susp-fmap h)) (SuspFmap.glue-β g (f a))
    ∙ SuspFmap.glue-β h (g (f a))

  left-β = β (fold {X = X}) winl projl
  right-β = β (fold {X = X}) winr projr

  left-reduce : ((ptd-susp-fmap {Y = X} ptd-fold
                 ∘ptd ptd-susp-fmap ptd-winl)
                 ∘ptd ptd-susp-fmap ptd-projl) ∘ptd ptd-diff
                == ptd-idf (Ptd-Susp X)
  left-reduce = ptd-λ=
    (Suspension-elim (fst X) idp (merid _ (snd X))
      (λ x → ↓-='-from-square $
        (ap-∘ (susp-fmap fold ∘ susp-fmap winl ∘ susp-fmap projl)
           diff (merid _ x)
         ∙ ap (ap (susp-fmap fold ∘ susp-fmap winl ∘ susp-fmap projl))
             (Diff.glue-β x)
         ∙ ap-∙ (susp-fmap fold ∘ susp-fmap winl ∘ susp-fmap projl)
               (merid _ (winl x)) (! (merid _ (winr x)))
         ∙ (left-β (winl x)
           ∙2 (ap-! (susp-fmap fold ∘ susp-fmap winl ∘ susp-fmap projl)
                 (merid _ (winr x))
               ∙ ap ! (left-β (winr x)))))
        ∙v⊡ (vid-square {p = merid _ x} ⊡h ru-square (merid _ (snd X)))
        ⊡v∙ (∙-unit-r _ ∙ ! (ap-idf (merid _ x)))))
    idp

  right-reduce : ((ptd-susp-fmap {Y = X} ptd-fold
                 ∘ptd ptd-susp-fmap ptd-winr)
                 ∘ptd ptd-susp-fmap ptd-projr) ∘ptd ptd-diff
                == ptd-flip-susp X
  right-reduce = ptd-λ=
    (Suspension-elim (fst X) (merid _ (snd X)) idp
      (λ x → ↓-='-from-square $
        (ap-∘ (susp-fmap fold ∘ susp-fmap winr ∘ susp-fmap projr)
           diff (merid _ x)
         ∙ ap (ap (susp-fmap fold ∘ susp-fmap winr ∘ susp-fmap projr))
             (Diff.glue-β x)
         ∙ ap-∙ (susp-fmap fold ∘ susp-fmap winr ∘ susp-fmap projr)
               (merid _ (winl x)) (! (merid _ (winr x)))
         ∙ (right-β (winl x)
           ∙2 (ap-! (susp-fmap fold ∘ susp-fmap winr ∘ susp-fmap projr)
                 (merid _ (winr x))
               ∙ ap ! (right-β (winr x)))))
        ∙v⊡ ((lt-square (merid _ (snd X)) ⊡h vid-square {p = ! (merid _ x)}))
        ⊡v∙ ! (FlipSusp.glue-β x)))
    (! (!-inv-r (merid _ (snd X))))

  C-β : {Y Z U V W : Ptd i} (k : fst (V ∙→ W))
    (h : fst (U ∙→ V)) (g : fst (Z ∙→ U)) (f : fst (Y ∙→ Z))
    → CF-hom n f ∘hom CF-hom n g ∘hom CF-hom n h ∘hom CF-hom n k
      == CF-hom n (((k ∘ptd h) ∘ptd g) ∘ptd f)
  C-β k h g f =
    ap (λ w → CF-hom n f ∘hom CF-hom n g ∘hom w) (! (CF-comp n k h))
    ∙ ap (λ w → CF-hom n f ∘hom w) (! (CF-comp n (k ∘ptd h) g))
    ∙ ! (CF-comp n ((k ∘ptd h) ∘ptd g) f)

  C-left-reduce = C-β (ptd-susp-fmap ptd-fold) (ptd-susp-fmap ptd-winl)
                      (ptd-susp-fmap ptd-projl) ptd-diff
                  ∙ ap (CF-hom n) left-reduce ∙ CF-ident n

  C-right-reduce = C-β (ptd-susp-fmap ptd-fold) (ptd-susp-fmap ptd-winr)
                       (ptd-susp-fmap ptd-projr) ptd-diff
                   ∙ ap (CF-hom n) right-reduce
