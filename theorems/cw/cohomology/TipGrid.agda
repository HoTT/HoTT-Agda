{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Theory
open import groups.Exactness
open import groups.HomSequence
open import groups.ExactSequence

open import cw.CW

module cw.cohomology.TipGrid {i} (OT : OrdinaryTheory i)
  (⊙skel : ⊙Skeleton {i} 1) (ac : ⊙has-cells-with-choice 0 ⊙skel i) where

open OrdinaryTheory OT
open import cw.cohomology.Descending OT
open import cw.cohomology.WedgeOfCells OT
import cohomology.LongExactSequence

{-
   X₀ --> X₁
   |      |
   v      v
   1 -> X₁/X₀
-}


private
  G : Group i
  G = C 0 (⊙Lift ⊙Bool)

  module LES n = cohomology.LongExactSequence cohomology-theory n (⊙cw-incl-last ⊙skel)

cw-co∂-head' : C 0 (⊙cw-head ⊙skel) →ᴳ C 1 (⊙Cofiber (⊙cw-incl-last ⊙skel))
cw-co∂-head' = LES.co∂ 0

cw-co∂-head : G ×ᴳ C 0 (⊙cw-head ⊙skel) →ᴳ C 1 (⊙Cofiber (⊙cw-incl-last ⊙skel))
cw-co∂-head = cw-co∂-head' ∘ᴳ ×ᴳ-snd {G = G} {H = C 0 (⊙cw-head ⊙skel)}

Ker-cw-co∂-head' : C 0 ⊙⟦ ⊙skel ⟧ ≃ᴳ Ker.grp cw-co∂-head'
Ker-cw-co∂-head' = Exact2.G-trivial-implies-H-iso-ker
  (exact-seq-index 2 $ LES.C-cofiber-exact-seq -1)
  (exact-seq-index 0 $ LES.C-cofiber-exact-seq 0)
  (C-Cofiber-cw-incl-last-<-is-trivial 0 ltS ⊙skel ac)

Ker-cw-co∂-head : G ×ᴳ C 0 ⊙⟦ ⊙skel ⟧ ≃ᴳ Ker.grp cw-co∂-head
Ker-cw-co∂-head = lemma ∘eᴳ ×ᴳ-emap (idiso G) Ker-cw-co∂-head' where
  lemma : G ×ᴳ Ker.grp cw-co∂-head' ≃ᴳ Ker.grp cw-co∂-head
  lemma = group-hom (λ{(g , (h , is-ker)) → ((g , h) , is-ker)})
    (λ _ _ → Subtype=-out (Ker.subEl-prop cw-co∂-head) idp) ,
    is-eq _ (λ{((g , h) , is-ker) → (g , (h , is-ker))}) (λ _ → idp) (λ _ → idp)

private
  -- separate lemmas to speed up the type checking
  abstract
    lemma₁-abelian : is-abelian (C 1 (⊙Cofiber (⊙cw-incl-last ⊙skel)))
    lemma₁-abelian = C-is-abelian 1 (⊙Cofiber (⊙cw-incl-last ⊙skel))

module CokerCo∂Head = Coker lemma₁-abelian cw-co∂-head

private
  -- separate lemmas to speed up the type checking
  abstract
    lemma₁-exact₀ : is-exact cw-co∂-head (C-fmap 1 (⊙cfcod' (⊙cw-incl-last ⊙skel)))
    lemma₁-exact₀ = pre∘-is-exact
      (×ᴳ-snd {G = G} {H = C 0 (⊙cw-head ⊙skel)})
      (×ᴳ-snd-is-surj {G = G} {H = C 0 (⊙cw-head ⊙skel)})
      (exact-seq-index 1 $ LES.C-cofiber-exact-seq 0)

    lemma₁-exact₁ : is-exact (C-fmap 1 (⊙cfcod' (⊙cw-incl-last ⊙skel)))
      (C-fmap 1 (⊙cw-incl-last ⊙skel))
    lemma₁-exact₁ = exact-seq-index 2 $ LES.C-cofiber-exact-seq 0

    lemma₁-trivial : is-trivialᴳ (C 1 (⊙cw-head ⊙skel))
    lemma₁-trivial = C-points-≠-is-trivial 1 (pos-≠ (ℕ-S≠O 0)) (⊙cw-init ⊙skel) (fst ac)

Coker-cw-co∂-head : CokerCo∂Head.grp ≃ᴳ C 1 ⊙⟦ ⊙skel ⟧
Coker-cw-co∂-head = Exact2.L-trivial-implies-coker-iso-K
  lemma₁-exact₀ lemma₁-exact₁ lemma₁-abelian lemma₁-trivial
