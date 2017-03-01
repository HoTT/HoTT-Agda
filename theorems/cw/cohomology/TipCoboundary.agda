{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import groups.Cokernel
open import groups.Exactness
open import groups.ExactSequence
open import cohomology.Theory

open import cw.CW

module cw.cohomology.TipCoboundary {i} (OT : OrdinaryTheory i)
  (⊙skel : ⊙Skeleton {i} 1) where

open OrdinaryTheory OT
open import cw.cohomology.TipAndAugment cohomology-theory (⊙cw-init ⊙skel)
open import cw.cohomology.WedgeOfCells OT
open import cohomology.LongExactSequence cohomology-theory 0 (⊙cw-incl-last ⊙skel)

CX₁/X₀-is-abelian = CXₙ/Xₙ₋₁-is-abelian ⊙skel

cw-co∂-head' : CX₀ →ᴳ CXₙ/Xₙ₋₁ ⊙skel
cw-co∂-head' = co∂

cw-co∂-head : G×CX₀ →ᴳ CXₙ/Xₙ₋₁ ⊙skel
cw-co∂-head = record {f = GroupHom.f cw-co∂-head' ∘ snd; pres-comp = lemma} where
  abstract lemma = ∘-pres-comp cw-co∂-head' (×ᴳ-snd {G = G} {H = CX₀})

abstract
  -- Somehow the [lemma] above still reduces here.  Maybe it is a bug?
  co∂-head-incl-exact : is-exact cw-co∂-head (C-fmap 1 (⊙cfcod' (⊙cw-incl-last ⊙skel)))
  co∂-head-incl-exact = pre∘-is-exact
    (×ᴳ-snd {G = G} {H = CX₀})
    (×ᴳ-snd-is-surj {G = G} {H = C 0 (⊙cw-head ⊙skel)})
    (exact-seq-index 1 C-cofiber-exact-seq)

module CokerCo∂Head where
  grp = Coker cw-co∂-head CX₁/X₀-is-abelian
  open Group grp public
