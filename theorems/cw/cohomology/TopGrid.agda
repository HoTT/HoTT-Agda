{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory

module cw.cohomology.TopGrid {i} (OT : OrdinaryTheory i)
  (n : ℤ) {X Y Z : Ptd i} (f : X ⊙→ Y) (g : Y ⊙→ Z) where

{-
  X --> Y ---> Z
  |     | this |
  v     v  one v
  1 -> Y/X -> Z/X
-}

  open OrdinaryTheory OT
  open import cohomology.PtdMapSequence cohomology-theory
  open import cw.cohomology.GridPtdMap f g using (Y/X-to-Z/X)

  top-grid-comm-sqr : CommSquare (fst g) (fst Y/X-to-Z/X) cfcod cfcod
  top-grid-comm-sqr = comm-sqr λ _ → idp

  C-top-grid-commutes : CommSquareᴳ
    (C-fmap n Y/X-to-Z/X) (C-fmap n g) (C-fmap n (⊙cfcod' (g ⊙∘ f))) (C-fmap n (⊙cfcod' f))
  C-top-grid-commutes = C-comm-square n top-grid-comm-sqr
