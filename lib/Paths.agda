{-# OPTIONS --without-K #-}

module lib.Paths where

open import lib.Base
open import lib.Empty

_=/=_ : ∀ {i} {A : Type i} → (A → A → Type i)
x =/= y = ¬ (x == y)

-- Infinity groupoid structure

infixr 8 _∘_  -- \o

_∘_ : ∀ {i} {A : Type i} {x y z : A}
  → (x == y → y == z → x == z)
q ∘ idp = q

-- Composition with the opposite definitional behaviour
_∘'_ : ∀ {i} {A : Type i} {x y z : A}
  → (x == y → y == z → x == z)
idp ∘' q = q

! : ∀ {i} {A : Type i} {x y : A}
  → (x == y → y == x)
! idp = idp


-- Equational reasoning combinator

infix  2 _∎
infixr 2 _=⟨_⟩_

_=⟨_⟩_ : ∀ {i} {A : Type i} (x : A) {y z : A} → x == y → y == z → x == z
_ =⟨ p ⟩ q = p ∘ q

_∎ : ∀ {i} {A : Set i} (x : A) → x == x
_∎ _ = idp
