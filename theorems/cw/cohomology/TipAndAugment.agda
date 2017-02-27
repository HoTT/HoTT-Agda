{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory

open import cw.CW

module cw.cohomology.TipAndAugment {i} (OT : OrdinaryTheory i)
  (⊙skel : ⊙Skeleton {i} 0) where

open OrdinaryTheory OT

G : Group i
G = C 0 (⊙Lift ⊙Bool)

G-is-abelian : is-abelian G
G-is-abelian = C-is-abelian 0 (⊙Lift ⊙Bool)

CX₀ : Group i
CX₀ = C 0 (⊙cw-head ⊙skel)

CX₀-is-abelian : is-abelian CX₀
CX₀-is-abelian = C-is-abelian 0 (⊙cw-head ⊙skel)

G×CX₀ : Group i
G×CX₀ = G ×ᴳ CX₀

abstract
  G×CX₀-is-abelian : is-abelian G×CX₀
  G×CX₀-is-abelian = ×ᴳ-is-abelian G CX₀ G-is-abelian CX₀-is-abelian

G×CX₀-abgroup : AbGroup i
G×CX₀-abgroup = G×CX₀ , G×CX₀-is-abelian

cw-coε : G →ᴳ G×CX₀
cw-coε = ×ᴳ-inl {G = G} {H = CX₀}
