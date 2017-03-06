{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory
open import groups.Cokernel
open import groups.Exactness
open import groups.HomSequence
open import groups.ExactSequence

open import cw.CW

module cw.cohomology.TipGrid {i} (OT : OrdinaryTheory i)
  (⊙skel : ⊙Skeleton {i} 1) (ac : ⊙has-cells-with-choice 0 ⊙skel i) where

open OrdinaryTheory OT
open import cw.cohomology.Descending OT
open import cw.cohomology.WedgeOfCells OT ⊙skel
open import cw.cohomology.TipAndAugment OT (⊙cw-init ⊙skel)
open import cw.cohomology.TipCoboundary OT ⊙skel
import cohomology.LongExactSequence

{-
   X₀ --> X₁
   |      |
   v      v
   1 -> X₁/X₀
-}

private
  module LES n = cohomology.LongExactSequence cohomology-theory n (⊙cw-incl-last ⊙skel)

Ker-cw-co∂-head' : C 0 ⊙⟦ ⊙skel ⟧ ≃ᴳ Ker cw-co∂-head'
Ker-cw-co∂-head' = Exact2.G-trivial-implies-H-iso-ker
  (exact-seq-index 2 $ LES.C-cofiber-exact-seq -1)
  (exact-seq-index 0 $ LES.C-cofiber-exact-seq 0)
  (CXₙ/Xₙ₋₁-<-is-trivial ltS ac)

{- NOT USED

Ker-cw-co∂-head : G ×ᴳ C 0 ⊙⟦ ⊙skel ⟧ ≃ᴳ Ker cw-co∂-head
Ker-cw-co∂-head = lemma ∘eᴳ ×ᴳ-emap (idiso G) Ker-cw-co∂-head' where
  lemma : G ×ᴳ Ker.grp cw-co∂-head' ≃ᴳ Ker.grp cw-co∂-head
  lemma = group-hom (λ{(g , (h , is-ker)) → ((g , h) , is-ker)})
    (λ _ _ → Subtype=-out (Ker.subEl-prop cw-co∂-head) idp) ,
    is-eq _ (λ{((g , h) , is-ker) → (g , (h , is-ker))}) (λ _ → idp) (λ _ → idp)
-}

private
  -- separate lemmas to speed up the type checking
  abstract
    lemma-exact₀ : is-exact (C-fmap 1 (⊙cfcod' (⊙cw-incl-last ⊙skel)))
      (C-fmap 1 (⊙cw-incl-last ⊙skel))
    lemma-exact₀ = exact-seq-index 2 $ LES.C-cofiber-exact-seq 0

    lemma-trivial : is-trivialᴳ (C 1 (⊙cw-head ⊙skel))
    lemma-trivial = CX₀-≠-is-trivial (pos-≠ (ℕ-S≠O 0))
      (⊙init-has-cells-with-choice ⊙skel ac)

Coker-cw-co∂-head : CokerCo∂Head.grp ≃ᴳ C 1 ⊙⟦ ⊙skel ⟧
Coker-cw-co∂-head = Exact2.L-trivial-implies-coker-iso-K
  co∂-head-incl-exact lemma-exact₀ CX₁/X₀-is-abelian lemma-trivial
