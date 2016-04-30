{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.ConstantToSetFactorization
  {i j} {A : Type i} {B : Type j} (B-is-set : is-set B)
  (f : A → B) (f-is-const : ∀ a₁ a₂ → f a₁ == f a₂) where

  private
    Skel = SetQuotient {A = A} (λ _ _ → Unit)

    abstract
      Skel-has-all-paths : has-all-paths Skel
      Skel-has-all-paths =
        SetQuot-elim (λ _ → Π-is-set λ _ → =-preserves-set SetQuotient-is-set)
          (λ a₁ →
            SetQuot-elim {P = λ s₂ → q[ a₁ ] == s₂}
              (λ _ → =-preserves-set SetQuotient-is-set)
              (λ _ → quot-rel _)
              (λ _ → prop-has-all-paths-↓ (SetQuotient-is-set _ _)))
          (λ {a₁ a₂} _ → ↓-cst→app-in λ s₂ →
              prop-has-all-paths-↓ (SetQuotient-is-set _ _))

    Skel-is-prop : is-prop Skel
    Skel-is-prop = all-paths-is-prop Skel-has-all-paths

    Skel-lift : Skel → B
    Skel-lift = SetQuot-rec B-is-set f (λ {a₁ a₂} _ → f-is-const a₁ a₂)

  cst-extend : Trunc -1 A → B
  cst-extend = Skel-lift ∘ Trunc-rec Skel-is-prop q[_]

  -- The beta rule.
  -- This is definitionally true, so you don't need it.
  cst-extend-β : cst-extend ∘ [_] == f
  cst-extend-β = idp
