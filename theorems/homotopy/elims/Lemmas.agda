{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module homotopy.elims.Lemmas where

fill-upper-right : ∀ {i j} {A : Type i} {B : A → Type j}
  {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
  {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ b₁₀' : B a₁₀} {b₁₁ : B a₁₁}
  (q₀₋ : b₀₀ == b₀₁ [ B ↓ p₀₋ ]) (q₋₀ : b₀₀ == b₁₀ [ B ↓ p₋₀ ])
  (q₋₁ : b₀₁ == b₁₁ [ B ↓ p₋₁ ]) (q₁₋ : b₁₀' == b₁₁ [ B ↓ p₁₋ ])
  → Σ (b₁₀ == b₁₀')
      (λ r → SquareOver B sq q₀₋ q₋₀ q₋₁ (r ◃ q₁₋))
fill-upper-right ids idp idp idp idp = (idp , ids)

fill-upper-right-unique : ∀ {i j} {A : Type i} {B : A → Type j}
  {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
  {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ b₁₀' : B a₁₀} {b₁₁ : B a₁₁}
  (q₀₋ : b₀₀ == b₀₁ [ B ↓ p₀₋ ]) (q₋₀ : b₀₀ == b₁₀ [ B ↓ p₋₀ ])
  (q₋₁ : b₀₁ == b₁₁ [ B ↓ p₋₁ ]) (q₁₋ : b₁₀' == b₁₁ [ B ↓ p₁₋ ])
  (r : b₁₀ == b₁₀')
  → SquareOver B sq q₀₋ q₋₀ q₋₁ (r ◃ q₁₋)
  → r == fst (fill-upper-right sq q₀₋ q₋₀ q₋₁ q₁₋)
fill-upper-right-unique {B = B} ids idp idp idp idp r sq' =
  ! (◃idp {B = B} r) ∙ ! (horiz-degen-path sq')
