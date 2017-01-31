{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module homotopy.ConstantToSetExtendsToProp {i j}
  {A : Type i} {B : Type j} (B-is-set : is-set B)
  (f : A → B) (f-is-const : ∀ a₁ a₂ → f a₁ == f a₂) where

  private
    Skel = SetQuot {A = A} (λ _ _ → Unit)

    abstract
      Skel-has-all-paths : has-all-paths Skel
      Skel-has-all-paths =
        SetQuot-elim (λ _ → Π-is-set λ _ → =-preserves-set SetQuot-is-set)
          (λ a₁ →
            SetQuot-elim {P = λ s₂ → q[ a₁ ] == s₂}
              (λ _ → =-preserves-set SetQuot-is-set)
              (λ _ → quot-rel _)
              (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _)))
          (λ {a₁ a₂} _ → ↓-Π-cst-app-in λ s₂ →
              prop-has-all-paths-↓ (SetQuot-is-set _ _))

    Skel-is-prop : is-prop Skel
    Skel-is-prop = all-paths-is-prop Skel-has-all-paths

    Skel-lift : Skel → B
    Skel-lift = SetQuot-rec B-is-set f (λ {a₁ a₂} _ → f-is-const a₁ a₂)

  ext : Trunc -1 A → B
  ext = Skel-lift ∘ Trunc-rec Skel-is-prop q[_]

  abstract
    ext-is-const : ∀ a₁ a₂ → ext a₁ == ext a₂
    ext-is-const = Trunc-elim
      (λ a₁ → Π-is-prop λ a₂ → B-is-set _ _)
      (λ a₁ → Trunc-elim (λ a₂ → B-is-set _ _)
        (λ a₂ → f-is-const a₁ a₂))

  private
    abstract
      -- The beta rule.
      -- This is definitionally true, so you don't need it.
      ext-β : ext ∘ [_] == f
      ext-β = idp
