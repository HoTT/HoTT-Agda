{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.OrdinaryTheory

{- Cohomology functor sends constant functions to constant functions -}

module cohomology.ConstantFunction {i} (OT : OrdinaryTheory i) where

open import cohomology.Unit OT
open OrdinaryTheory OT

module _ (n : ℕ) {X Y : Ptd i} where

  C-cst : CF-hom n (ptd-cst {X = X} {Y = Y}) == cst-hom
  C-cst =
    CF-hom n (ptd-cst {X = PLU} ∘ptd ptd-cst {X = X})
      =⟨ CF-comp n ptd-cst ptd-cst ⟩
    (CF-hom n (ptd-cst {X = X})) ∘hom (CF-hom n (ptd-cst {X = PLU}))
      =⟨ hom= (CF-hom n (ptd-cst {X = PLU})) cst-hom
              (λ= (λ _ → prop-has-all-paths (C-Unit-is-prop n) _ _))
         |in-ctx (λ w → CF-hom n (ptd-cst {X = X} {Y = PLU}) ∘hom w) ⟩
    (CF-hom n (ptd-cst {X = X} {Y = PLU})) ∘hom cst-hom
      =⟨ pre∘-cst-hom (CF-hom n (ptd-cst {X = X} {Y = PLU})) ⟩
    cst-hom ∎
    where
    PLU = Ptd-Lift {j = i} Ptd-Unit

