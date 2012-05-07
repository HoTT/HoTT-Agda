{-# OPTIONS --without-K #-}

open import Types

module Functions where

-- Identity functions

idmap : ∀ {i} (A : Set i) → (A → A)
idmap A = λ x → x

-- Constant functions

cstmap : ∀ {i j} {A : Set i} {B : Set j} (b : B) → (A → B)
cstmap b = λ _ → b

-- Function composition

_◯_ : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} (g : B → C) (f : A → B) → (A → C)  -- \bigcirc
g ◯ f = λ x → g (f x)
