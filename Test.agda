open import Base

module Test (A : Set) where

postulate
  a : A
  f : ⦃ x : A ⦄ → Set

g : Set
g = f

-- h : Set
-- h = f
