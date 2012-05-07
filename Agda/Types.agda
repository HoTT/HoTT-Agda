{-# OPTIONS --without-K #-}

module Types where

-- Universe levels

postulate  -- Universe levels
  Level : Set
  zero-u : Level
  suc : Level → Level
  max : Level → Level → Level

{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO zero-u #-}
{-# BUILTIN LEVELSUC suc #-}
{-# BUILTIN LEVELMAX max #-}

-- Empty type

data ⊥ : Set where  -- \bot

abort : ∀ {i} (A : Set i) → (⊥ → A)
abort A ()

-- Unit type

-- I need a universe polymorphic [unit]
record unit {i} : Set i where
  constructor tt

-- Booleans

data bool : Set where
  true : bool
  false : bool

-- Dependent sum

record Σ {i j} (A : Set i) (P : A → Set j) : Set (max i j) where  -- \Sigma
  constructor _,_
  field
    π₁ : A       -- \pi\_1
    π₂ : P (π₁)  -- \pi\_2
open Σ public

-- Product

_×_ : ∀ {i j} (A : Set i) (B : Set j) → Set (max i j)
A × B = Σ A (λ _ → B)

-- Natural numbers

data ℕ : Set where  -- \bn
  O : ℕ
  S : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO O #-}
{-# BUILTIN SUC S #-}

-- Integers

data ℤ : Set where  -- \bz
  O : ℤ
  pos : ℕ → ℤ
  neg : ℕ → ℤ
