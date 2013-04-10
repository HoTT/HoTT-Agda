{-# OPTIONS --without-K #-}

open import Base

module Homotopy.Cover.Def {i} (A : Set i) where

record covering : Set (suc i) where
  constructor cov[_,_]
  field
    fiber : A → Set i
    fiber-is-set : ∀ a → is-set (fiber a)

open import Homotopy.Truncation
open import Homotopy.Connected
open import Homotopy.PathTruncation

-- In terms of connectedness
is-universal : covering → Set i
is-universal cov[ fiber , _ ] = is-connected ⟨1⟩ $ Σ A fiber

-- In terms of connectedness
universal-covering : Set (suc i)
universal-covering = Σ covering is-universal

tracing : ∀ cov → let open covering cov in
  ∀ {a₁ a₂} → fiber a₁ → a₁ ≡₀ a₂ → fiber a₂
tracing cov[ fiber , fiber-is-set ] y =
  π₀-extend-nondep
    ⦃ fiber-is-set _ ⦄
    (λ p → transport fiber p y)

compose-tracing : ∀ cov → let open covering cov in
  ∀ {a₁ a₂ a₃} y (p₁ : a₁ ≡₀ a₂) (p₂ : a₂ ≡₀ a₃)
  → tracing cov (tracing cov y p₁) p₂ ≡ tracing cov y (p₁ ∘₀ p₂)
compose-tracing cov y = let open covering cov in
  π₀-extend
    ⦃ λ _ → Π-is-set λ _ → ≡-is-set $ fiber-is-set _ ⦄
    (λ p₁ → π₀-extend
      ⦃ λ _ → ≡-is-set $ fiber-is-set _ ⦄
      (λ p₂ → compose-trans fiber p₂ p₁ y))

covering-eq : ∀ {co₁ co₂ : covering}
  → covering.fiber co₁ ≡ covering.fiber co₂
  → co₁ ≡ co₂
covering-eq {cov[ _ , set₁ ]} {cov[ ._ , set₂ ]} refl =
  ap (λ set → cov[ _ , set ])
    (prop-has-all-paths (Π-is-prop λ _ → is-set-is-prop) _ _)
