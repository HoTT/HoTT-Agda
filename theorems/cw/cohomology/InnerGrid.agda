{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Theory

module cw.cohomology.InnerGrid {i} (OT : OrdinaryTheory i)
  (n : ℤ) {X Y Z W : Ptd i} (f : X ⊙→ Y) (g : Y ⊙→ Z) (h : Z ⊙→ W) where

  open OrdinaryTheory OT
  open import cohomology.PtdMapSequence cohomology-theory

{-

  X --> Y ---> Z ---> W
  |     |      |      |
  v     |      v      v
  1 ----+---> Z/X -> W/X
        |      | this |
        v      v  one v
        1 --> Z/Y -> W/Y

-}

  import cw.cohomology.GridPtdMap

  open cw.cohomology.GridPtdMap (g ⊙∘ f) h using ()
    renaming (Y/X-to-Z/X to Z/X-to-W/X; B/A-to-C/A to C/A-to-D/A;
      module B/AToC/A to C/AToD/A)

  open cw.cohomology.GridPtdMap f g
    using (Z/X-to-Z/Y; C/A-to-C/B; module C/AToC/B)

  open cw.cohomology.GridPtdMap f (h ⊙∘ g) using ()
    renaming (Z/X-to-Z/Y to W/X-to-W/Y; C/A-to-C/B to D/A-to-D/B;
      module C/AToC/B to D/AToD/B)

  open cw.cohomology.GridPtdMap g h using ()
    renaming (Y/X-to-Z/X to Z/Y-to-W/Y; B/A-to-C/A to C/B-to-D/B;
      module B/AToC/A to C/BToD/B)

  inner-grid-comm-sqr : CommSquare C/A-to-D/A C/B-to-D/B C/A-to-C/B D/A-to-D/B
  inner-grid-comm-sqr = comm-sqr $ Cofiber-elim idp (λ _ → idp)
    (λ a → ↓-='-in' $ ap-∘ C/B-to-D/B C/A-to-C/B (glue a)
                    ∙ ap (ap C/B-to-D/B) (C/AToC/B.glue-β a)
                    ∙ C/BToD/B.glue-β ((fst f) a)
                    ∙ ! (D/AToD/B.glue-β a)
                    ∙ ap (ap D/A-to-D/B) (! (C/AToD/A.glue-β a))
                    ∙ ∘-ap D/A-to-D/B C/A-to-D/A (glue a))

  C-inner-grid-commutes : CommSquareᴳ
    (C-fmap n Z/Y-to-W/Y) (C-fmap n Z/X-to-W/X) (C-fmap n W/X-to-W/Y) (C-fmap n Z/X-to-Z/Y)
  C-inner-grid-commutes = C-comm-square n inner-grid-comm-sqr
