{-# OPTIONS --without-K #-}

open import Types

module Functions where

-- Identity functions
id : ∀ {i} (A : Set i) → (A → A)
id A = λ x → x

-- Constant functions
cst : ∀ {i j} {A : Set i} {B : Set j} (b : B) → (A → B)
cst b = λ _ → b

-- Composition of dependent functions
_◯_ : ∀ {i j k} {A : Set i} {B : A → Set j} {C : (a : A) → (B a → Set k)}
  → (g : {a : A} → Π (B a) (C a)) → (f : Π A B) → Π A (λ a → C a (f a))
g ◯ f = λ x → g (f x)
