{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module cw.cohomology.GridPtdMap {i j k}
  {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (f : X ⊙→ Y) (g : Y ⊙→ Z) where

  open import cw.cohomology.GridMap (fst f) (fst g) public

  Y/X = ⊙Cofiber f
  Z/X = ⊙Cofiber (g ⊙∘ f)
  Z/Y = ⊙Cofiber g

  Y/X-to-Z/X : Y/X ⊙→ Z/X
  Y/X-to-Z/X = B/A-to-C/A , idp

  Z/X-to-Z/Y : Z/X ⊙→ Z/Y
  Z/X-to-Z/Y = C/A-to-C/B , idp
