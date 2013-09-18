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
infixr 20 _◯_
_◯_ : ∀ {i j k} {A : Set i} {B : A → Set j} {C : (a : A) → (B a → Set k)}
  → (g : {a : A} → Π (B a) (C a)) → (f : Π A B) → Π A (λ a → C a (f a))
g ◯ f = λ x → g (f x)

-- Application
infixr 0 _$_
_$_ : ∀ {i j} {A : Set i} {B : A → Set j} → (∀ x → B x) → (∀ x → B x)
f $ x = f x

-- Curry! Can't live without it!
curry : ∀ {i j k} {A : Set i} {B : A → Set j} {C : Σ A B → Set k}
  → (∀ s → C s) → (∀ x y → C (x , y))
curry f x y = f (x , y)

uncurry : ∀ {i j k} {A : Set i} {B : A → Set j} {C : ∀ x → B x → Set k}
  → (∀ x y → C x y) → (∀ s → C (π₁ s) (π₂ s))
uncurry f (x , y) = f x y
