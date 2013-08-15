{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NConnected
open import lib.types.TLevel
open import lib.NType2
open import lib.types.Pi

module lib.types.Covering {i} where

{-
  The definition of covering spaces.
-}
record Covering (X : Type i) {j} : Type (lmax i (lsucc j)) where
  constructor covering
  field
    fiber : X → Type j
    fiber-is-set : ∀ x → is-set (fiber x)

module _ {X : Type i} {j} where

  open Covering

  private
    covering=′ : (c₁ c₂ : Covering X {j}) → fiber c₁ == fiber c₂ → c₁ == c₂
    covering=′ (covering f _) (covering .f _) idp = ap (covering f) $
      prop-has-all-paths (Π-is-prop λ _ → is-set-is-prop) _ _

  covering= : (c₁ c₂ : Covering X {j}) → (∀ x → fiber c₁ x ≃ fiber c₂ x)
    → c₁ == c₂
  covering= c₁ c₂ fiber≃ = covering=′ c₁ c₂ (λ= λ x → ua $ fiber≃ x)

  -- The definition of universality in terms of connectedness.
  is-universal : Covering X {j} → Type (lmax i j)
  is-universal (covering fiber _) = is-connected ⟨1⟩ $ Σ X fiber

  -- In terms of connectedness
  universal-covering : Type (lmax i (lsucc j))
  universal-covering = Σ (Covering X {j}) is-universal

{-
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
-}
