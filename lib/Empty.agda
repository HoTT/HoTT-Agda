{-# OPTIONS --without-K #-}

module lib.Empty where

open import lib.Base
open import lib.NType

Empty = ⊥
Empty₀ = ⊥ {zero}
Empty0 = ⊥ {zero}
⊥₀ = ⊥ {zero}
⊥0 = ⊥ {zero}

⊥-elim : ∀ {i j} {P : ⊥ {i} → Type j} → ((x : ⊥) → P x)
⊥-elim ()

⊥-is-prop : ∀ {i} → is-prop (⊥ {i})
⊥-is-prop ()
