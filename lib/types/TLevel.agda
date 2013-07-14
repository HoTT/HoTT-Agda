{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.types.Nat

module lib.types.TLevel where

_-2 : ℕ → ℕ₋₂
O -2 = ⟨-2⟩
(S n) -2 = S (n -2)

_-1 : ℕ → ℕ₋₂
O -1 = ⟨-1⟩
(S n) -1 = S (n -1)

⟨_⟩ : ℕ → ℕ₋₂
⟨ n ⟩ = S (n -1)

⟨1⟩ = ⟨ 1 ⟩
⟨2⟩ = ⟨ 2 ⟩

_+2+_ : ℕ₋₂ → ℕ₋₂ → ℕ₋₂
⟨-2⟩ +2+ n = n
S m +2+ n = S (m +2+ n)

+2+-comm : (m n : ℕ₋₂) → m +2+ n == n +2+ m
+2+-comm ⟨-2⟩ n = n+2-2=n n  where

  n+2-2=n : (n : ℕ₋₂) → n == n +2+ ⟨-2⟩
  n+2-2=n ⟨-2⟩ = idp
  n+2-2=n (S n) = ap S (n+2-2=n n)

+2+-comm (S m) n = ap S (+2+-comm m n) ∙ swapS n m where

  swapS : (n m : ℕ₋₂) → S n +2+ m == n +2+ S m
  swapS ⟨-2⟩ m = idp
  swapS (S n) m = ap S (swapS n m)


_≤T_ : ℕ₋₂ → ℕ₋₂ → Type₀
⟨-2⟩ ≤T _ = Unit
(S m) ≤T ⟨-2⟩ = Empty
(S m) ≤T (S n) = (m ≤T n)

minT : ℕ₋₂ → ℕ₋₂ → ℕ₋₂
minT ⟨-2⟩ n = ⟨-2⟩
minT (S m) ⟨-2⟩ = ⟨-2⟩
minT (S m) (S n) = S (minT m n)

minT≤l : (m n : ℕ₋₂) → minT m n ≤T m
minT≤l ⟨-2⟩ _ = unit
minT≤l (S _) ⟨-2⟩ = unit
minT≤l (S m) (S n) = minT≤l m n

minT≤r : (m n : ℕ₋₂) → minT m n ≤T n
minT≤r ⟨-2⟩ _ = unit
minT≤r (S _) ⟨-2⟩ = unit
minT≤r (S m) (S n) = minT≤r m n

minT= : (m n : ℕ₋₂) → Coprod (minT m n == m) (minT m n == n)
minT= ⟨-2⟩ _ = inl idp
minT= (S _) ⟨-2⟩ = inr idp
minT= (S m) (S n) with minT= m n
minT= (S m) (S n) | inl p = inl (ap S p)
minT= (S m) (S n) | inr q = inr (ap S q)
