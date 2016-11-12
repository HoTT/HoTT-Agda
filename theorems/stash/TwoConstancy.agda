{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import experimental.TwoConstancyHIT

module experimental.TwoConstancy
  {i j} {A : Type i} {B : Type j} (B-is-gpd : is-gpd B)
  (f : A → B)
  (f-is-const₀ : ∀ a₁ a₂ → f a₁ == f a₂)
  (f-is-const₁ : ∀ a₁ a₂ a₃
    → f-is-const₀ a₁ a₂ ∙' f-is-const₀ a₂ a₃ == f-is-const₀ a₁ a₃) where

  private
    abstract
      lemma₁ : ∀ a (t₂ : TwoConstancy A) → point a == t₂
      lemma₁ a = TwoConstancy-elim {P = λ t₂ → point a == t₂}
        (λ _ → =-preserves-level 1 TwoConstancy-level)
        (λ b → link₀ a b)
        (λ b₁ b₂ → ↓-cst=idf-in' $ link₁ a b₁ b₂)
        (λ b₁ b₂ b₃ → set-↓-has-all-paths-↓ $ TwoConstancy-level _ _ )

      lemma₂ : ∀ (a₁ a₂ : A) →
        lemma₁ a₁ == lemma₁ a₂ [ (λ t₁ → ∀ t₂ → t₁ == t₂) ↓ link₀ a₁ a₂ ]
      lemma₂ a₁ a₂ = ↓-cst→app-in $
        TwoConstancy-elim
          {P = λ t₂ → lemma₁ a₁ t₂ == lemma₁ a₂ t₂ [ (λ t₁ → t₁ == t₂) ↓ link₀ a₁ a₂ ]}
          (λ _ → ↓-preserves-level 1 $ =-preserves-level 1 TwoConstancy-level)
          (λ b → ↓-idf=cst-in $ ! $ link₁ a₁ a₂ b)
          (λ b₁ b₂ → prop-has-all-paths-↓ $ ↓-level $ TwoConstancy-level _ _)
          (λ b₁ b₂ b₃ → prop-has-all-paths-↓ $ contr-is-prop
            $ ↓-level $ ↓-level $ TwoConstancy-level _ _)

      TwoConstancy-has-all-paths : has-all-paths (TwoConstancy A)
      TwoConstancy-has-all-paths =
        TwoConstancy-elim {P = λ t₁ → ∀ t₂ → t₁ == t₂}
          (λ _ → Π-level λ _ → =-preserves-level 1 TwoConstancy-level)
          lemma₁
          lemma₂
          (λ a₁ a₂ a₃ → prop-has-all-paths-↓
            $ ↓-level $ Π-is-set λ t₂ → TwoConstancy-level _ t₂)

  TwoConstancy-is-prop : is-prop (TwoConstancy A)
  TwoConstancy-is-prop = all-paths-is-prop TwoConstancy-has-all-paths

  cst-extend : Trunc -1 A → B
  cst-extend = TwoConstancy-rec B-is-gpd f f-is-const₀ f-is-const₁
             ∘ Trunc-rec TwoConstancy-is-prop point

  -- The beta rule.
  -- This is definitionally true, so you don't need it.
  cst-extend-β : cst-extend ∘ [_] == f
  cst-extend-β = idp
