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
open import cw.cohomology.TipAndAugment OT (⊙cw-init ⊙skel)
open import cw.cohomology.WedgeOfCells OT ⊙skel
open import cohomology.LongExactSequence cohomology-theory 0 (⊙cw-incl-last ⊙skel)

CX₁/X₀-is-abelian = CXₙ/Xₙ₋₁-is-abelian 1

cw-co∂-head' : CX₀ 0 →ᴳ CXₙ/Xₙ₋₁ 1
cw-co∂-head' = co∂

cw-co∂-head : C2×CX₀ 0 →ᴳ CXₙ/Xₙ₋₁ 1
cw-co∂-head = record {f = GroupHom.f cw-co∂-head' ∘ snd; pres-comp = lemma}
  where abstract lemma = ∘ᴳ-pres-comp cw-co∂-head' (×ᴳ-snd {G = C2 0} {H = CX₀ 0})

abstract
  -- This relies on the [lemma] above being non-abstract within this scope.
  co∂-head-incl-exact : is-exact cw-co∂-head (C-fmap 1 (⊙cfcod' (⊙cw-incl-last ⊙skel)))
  co∂-head-incl-exact = pre∘-is-exact
    (×ᴳ-snd {G = C2 0} {H = CX₀ 0})
    (×ᴳ-snd-is-surj {G = C2 0} {H = CX₀ 0})
    (exact-seq-index 1 C-cofiber-exact-seq)

module CokerCo∂Head where
  grp = Coker cw-co∂-head CX₁/X₀-is-abelian
  open Group grp public
