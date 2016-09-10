{-# OPTIONS --without-K #-}

open import HoTT

module experimental.CubicalTypes where

data access : ℕ → ℕ → Type₀ where
  [] : access O O
  _#up : ∀ {n} {k} → access n k → access (S n) k
  _#down : ∀ {n} {k} → access n k → access (S n) k
  _#keep : ∀ {n} {k} → access n k → access (S n) (S k)

_a∙_ : ∀ {n k l} → access n k → access k l → access n l
_a∙_ [] a₂ = a₂
_a∙_ (a₁ #up) a₂ = (a₁ a∙ a₂) #up
_a∙_ (a₁ #down) a₂ = (a₁ a∙ a₂) #down
_a∙_ (a₁ #keep) (a₂ #up) = (a₁ a∙ a₂) #up
_a∙_ (a₁ #keep) (a₂ #down) = (a₁ a∙ a₂) #down
_a∙_ (a₁ #keep) (a₂ #keep) = (a₁ a∙ a₂) #keep

