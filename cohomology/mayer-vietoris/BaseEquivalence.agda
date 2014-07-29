{-# OPTIONS --without-K #-}

open import HoTT

module cohomology.mayer-vietoris.BaseEquivalence {i} {A B : Type i}
  (Z : Ptd i) (f : fst Z → A) (g : fst Z → B) where

open import cohomology.mayer-vietoris.BaseEquivMaps Z f g
open import cohomology.mayer-vietoris.BaseRightInverse Z f g
open import cohomology.mayer-vietoris.BaseLeftInverse Z f g
open import cohomology.mayer-vietoris.Functions ps

base-equiv : Cofiber reglue ≃ Suspension (fst Z)
base-equiv = equiv into out into-out out-into

base-path : Cofiber reglue == Suspension (fst Z)
base-path = ua base-equiv

base-ptd-path : Ptd-Cof ptd-reglue == Ptd-Susp Z
base-ptd-path = ptd-ua base-equiv idp
