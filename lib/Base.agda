{-# OPTIONS --without-K #-}

module lib.Base where

-- Universe levels

postulate  -- Universe levels
  ULevel : Set
  zero : ULevel
  suc : ULevel → ULevel
  max : ULevel → ULevel → ULevel

{-# BUILTIN LEVEL ULevel #-}
{-# BUILTIN LEVELZERO zero #-}
{-# BUILTIN LEVELSUC suc #-}
{-# BUILTIN LEVELMAX max #-}


-- Universes

Type : (i : ULevel) → Set (suc i)
Type i = Set i

Type₀ = Set₀
Type0 = Set0

Type₁ = Set₁
Type1 = Set1


-- Identity type

-- Identity type
infixr 4 _==_

data _==_ {i} {A : Type i} (a : A) : A → Type i where
  idp : a == a

Paths = _==_

-- -- This should not be provable
-- K : {A : Set} → (x : A) → (p : x == x) → p == idp
-- K x p = {!p!}

ap : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y : A}
  → (x == y → f x == f y)
ap f idp = idp

-- Make equational reasoning much more readable
syntax ap f p = p |in-ctx f

transport : ∀ {i j} {A : Type i} (P : A → Type j) {x y : A}
  → (x == y → P x → P y)
transport P idp t = t
