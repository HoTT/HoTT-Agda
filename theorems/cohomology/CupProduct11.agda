{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane
open import homotopy.EilenbergMacLane1 using (EM₁-level₁)
open import homotopy.EM1HSpace
open import homotopy.EM1HSpaceAssoc
open import lib.types.TwoSemiCategory
open import lib.two-semi-categories.FundamentalCategory
open import lib.two-semi-categories.FunCategory

module cohomology.CupProduct11 {i} (R : CRing i) where

  open import cohomology.CupProduct01 R renaming (eq' to Pi2HSusp-eq'; comp to Pi2HSusp-comp)

  open EMExplicit R.add-ab-group

  module CP₁₁ where

    F : TwoSemiFunctor (group-to-cat R₊) (2-type-fundamental-cat (EM₁ R₊ → EM 2))
    F =
      ab-group-cat-to-dual R.add-ab-group –F→
      group-op-to-EM₁→EM₂ –F→
      λ=-functor (EM₁ R₊) (EM 2)

    cp₁₁ : EM₁ R₊ → EM₁ R₊ → EM 2
    cp₁₁ =
      EM₁-rec
        {C = EM₁ R₊ → EM 2}
        F
