{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.Theory

{- Cohomology functor sends constant functions to constant functions -}

module cohomology.ConstantFunction {i} (CT : CohomologyTheory i) where

open import cohomology.Unit CT
open CohomologyTheory CT

module _ (n : ℤ) {X Y : Ptd i} where

  CF-cst : CF-hom n (⊙cst {X = X} {Y = Y}) == cst-hom
  CF-cst =
    CF-hom n (⊙cst {X = PLU} ⊙∘ ⊙cst {X = X})
      =⟨ CF-comp n ⊙cst ⊙cst ⟩
    (CF-hom n (⊙cst {X = X})) ∘hom (CF-hom n (⊙cst {X = PLU}))
      =⟨ hom= (CF-hom n (⊙cst {X = PLU})) cst-hom
              (λ= (λ _ → prop-has-all-paths (C-Unit-is-prop n) _ _))
         |in-ctx (λ w → CF-hom n (⊙cst {X = X} {Y = PLU}) ∘hom w) ⟩
    (CF-hom n (⊙cst {X = X} {Y = PLU})) ∘hom cst-hom
      =⟨ pre∘-cst-hom (CF-hom n (⊙cst {X = X} {Y = PLU})) ⟩
    cst-hom ∎
    where
    PLU = ⊙Lift {j = i} ⊙Unit

