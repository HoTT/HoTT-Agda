{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.ConstantToSetFactorization
  {i j} {A : Type i} {B : Type j} (B-is-set : is-set B)
  (f : A → B) (f-is-const : ∀ a₁ a₂ → f a₁ == f a₂) where

  private
    Skel : Type i
    Skel = Trunc ⟨0⟩ (OneSkeleton f)

    abstract
      Skel-has-all-paths : has-all-paths Skel
      Skel-has-all-paths =
        Trunc-elim (λ _ → Π-is-set λ _ → =-preserves-set Trunc-level)
          (OneSkeleton-elim {P = λ s₁ → ∀ [s₂] → [ s₁ ] == [s₂]}
            (λ a₁ → Trunc-elim (λ _ → =-preserves-set Trunc-level)
              (OneSkeleton-elim {P = λ s₂ → [ point a₁ ] == [ s₂ ]}
                (λ a₂ → ap [_] $ link a₁ a₂ $ f-is-const a₁ a₂)
                (λ _ _ _ → prop-has-all-paths-↓ (Trunc-level {n = ⟨0⟩} _ _))))
            (λ a₁ a₂ p → ↓-cst→app-in λ s₂ →
              prop-has-all-paths-↓ (Trunc-level {n = ⟨0⟩} _ _)))

    Skel-is-prop : is-prop Skel
    Skel-is-prop = all-paths-is-prop Skel-has-all-paths

  cst-extend : Trunc ⟨-1⟩ A → B
  cst-extend = Trunc-rec B-is-set OneSkeleton-lift
             ∘ Trunc-rec Skel-is-prop ([_] ∘ point)

  -- The beta rule.
  -- This is definitionally true, so you don't need it.
  cst-extend-β : cst-extend ∘ [_] == f
  cst-extend-β = idp
