{-# OPTIONS --without-K #-}

open import Types

module Functions where

-- Identity functions

id : ∀ {i} (A : Set i) → (A → A)
id A = λ x → x

-- Constant functions

cst : ∀ {i j} {A : Set i} {B : Set j} (b : B) → (A → B)
cst b = λ _ → b

-- Function composition

_◯_ : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} -- \bigcirc
  → ((B → C) → (A → B) → (A → C)) 
g ◯ f = λ x → g (f x)
