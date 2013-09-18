{-# OPTIONS --without-K #-}

module Types where

-- Universe levels

postulate  -- Universe levels
  Level : Set
  zero : Level
  suc : Level → Level
  max : Level → Level → Level

{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO zero #-}
{-# BUILTIN LEVELSUC suc #-}
{-# BUILTIN LEVELMAX max #-}

-- Empty type

data ⊥ {i} : Set i where  -- \bot

abort : ∀ {i j} {P : ⊥ {i} → Set j} → ((x : ⊥) → P x)
abort ()

abort-nondep : ∀ {i j} {A : Set j} → (⊥ {i} → A)
abort-nondep ()

¬ : ∀ {i} (A : Set i) → Set i
¬ A = A → ⊥ {zero}

-- Unit type

record unit {i} : Set i where
  constructor tt

⊤ = unit  -- \top

-- Booleans

data bool {i} : Set i where
  true : bool
  false : bool

-- Dependent sum

record Σ {i j} (A : Set i) (P : A → Set j) : Set (max i j) where  -- \Sigma
  constructor _,_
  field
    π₁ : A       -- \pi\_1
    π₂ : P (π₁)  -- \pi\_2
open Σ public

-- Disjoint sum

data _⊔_ {i j} (A : Set i) (B : Set j) : Set (max i j) where  -- \sqcup
  inl : A → A ⊔ B
  inr : B → A ⊔ B

-- Product
_×_ : ∀ {i j} (A : Set i) (B : Set j) → Set (max i j)  -- \times
A × B = Σ A (λ _ → B)

-- Dependent product
Π : ∀ {i j} (A : Set i) (P : A → Set j) → Set (max i j)
Π A P = (x : A) → P x

-- Natural numbers

data ℕ : Set where  -- \bn
  O : ℕ
  S : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO O #-}
{-# BUILTIN SUC S #-}

-- Truncation index (isomorphic to the type of integers ≥ -2)

data ℕ₋₂ : Set where
  ⟨-2⟩ : ℕ₋₂
  S : (n : ℕ₋₂) → ℕ₋₂

⟨-1⟩ : ℕ₋₂
⟨-1⟩ = S ⟨-2⟩

⟨0⟩ : ℕ₋₂
⟨0⟩ = S ⟨-1⟩

_-2 : ℕ → ℕ₋₂
O -2 = ⟨-2⟩
(S n) -2 = S (n -2)

_-1 : ℕ → ℕ₋₂
n -1 = (S n) -2

⟨_⟩ : ℕ → ℕ₋₂
⟨ n ⟩ = S (n -1)

⟨1⟩ = ⟨ 1 ⟩
⟨2⟩ = ⟨ 2 ⟩

_+2+_ : ℕ₋₂ → ℕ₋₂ → ℕ₋₂
⟨-2⟩ +2+ n = n
S m +2+ n = S (m +2+ n)

-- Integers

data ℤ : Set where  -- \bz
  O : ℤ
  pos : (n : ℕ) → ℤ
  neg : (n : ℕ) → ℤ

-- Lifting

record lift {i} (j : Level) (A : Set i) : Set (max i j) where
  constructor ↑  -- \u
  field
    ↓ : A  -- \d
open lift public
