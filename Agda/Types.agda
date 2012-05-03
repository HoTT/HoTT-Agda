{-# OPTIONS --without-K #-}

-- Basic types

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

data empty {i : Level} : Set i where

abort : {i j : Level} (A : Set i) → (empty {j} → A)
abort A ()

-- Unit type

record unit {i : Level} : Set i where
  constructor tt

-- Booleans

data bool {i : Level} : Set i where
  true : bool
  false : bool

-- Dependent sum

record Σ {i j : Level} (A : Set i) (P : A → Set j) : Set (max i j) where  -- \Sigma
  constructor _,_
  field
    π₁ : A       -- \pi\_1
    π₂ : P (π₁)  -- \pi\_2
open Σ public

-- Product

infix 4 _×_

_×_ : {i j : Level} (A : Set i) (B : Set j) → Set (max i j)
A × B = Σ A (λ _ → B)

-- Naturals

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
