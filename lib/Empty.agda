{-# OPTIONS --without-K #-}

module lib.Empty where

open import lib.Base

data ⊥ {i} : Type i where  -- \bot

Empty = ⊥
Empty₀ = ⊥ {zero}
Empty0 = ⊥ {zero}
⊥₀ = ⊥ {zero}
⊥0 = ⊥ {zero}

⊥-elim : ∀ {i j} {P : ⊥ {i} → Set j} → ((x : ⊥) → P x)
⊥-elim ()

⊥-rec : ∀ {i j} {A : Set j} → (⊥ {i} → A)
⊥-rec ()

¬ : ∀ {i} (A : Type i) → Type i
¬ A = A → ⊥₀
