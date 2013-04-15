{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.NType
open import lib.Unit

module lib.Equivalences where

record is-equiv {i j} {A : Type i} {B : Type j} (f : A → B) : Type (max i j)
  where
  field
    g : B → A
    f-g : (b : B) → f (g b) == b
    g-f : (a : A) → g (f a) == a
    adj : (a : A) → ap f (g-f a) == f-g (f a)

is-eq : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
  (g : B → A) (f-g : (b : B) → f (g b) == b)
  (g-f : (a : A) → g (f a) == a) → is-equiv f
is-eq {A = A} {B = B} f g f-g g-f =
  record {g = g; f-g = f-g'; g-f = g-f; adj = adj} where
    f-g' : (b : B) → f (g b) == b
    f-g' b = ! (ap (f ∘ g) (f-g b)) ∙ ap f (g-f (g b)) ∙ f-g b

    postulate  -- TODO
      adj : (a : A) → ap f (g-f a) == f-g' (f a)
--    adj a = {!!}

_≃_ : ∀ {i j} (A : Type i) (B : Type j) → Type (max i j)
A ≃ B = Σ (A → B) is-equiv

Equiv = _≃_

equiv : ∀ {i j} {A : Type i} {B : Type j}
  (f : A → B) (g : B → A) (f-g : (b : B) → f (g b) == b)
  (g-f : (a : A) → g (f a) == a) → A ≃ B
equiv f g f-g g-f = (f , is-eq f g f-g g-f)

postulate  -- TODO
  is-equiv-is-prop : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
    → is-prop (is-equiv f)

_☆_ : ∀ {i j} {A : Type i} {B : Type j} (f : A ≃ B) (a : A) → B
f ☆ a = (fst f) a

inverse : ∀ {i} {j} {A : Set i} {B : Set j} (f : A ≃ B) → (B → A)
inverse (f , f-is-equiv) = is-equiv.g f-is-equiv

inverse-inv-l : ∀ {i} {j} {A : Set i} {B : Set j} (f : A ≃ B) (a : A)
  → (inverse f (f ☆ a) == a)
inverse-inv-l (f , f-is-equiv) a = is-equiv.g-f f-is-equiv a

inverse-inv-r : ∀ {i} {j} {A : Set i} {B : Set j} (f : A ≃ B) (b : B)
  → (f ☆ (inverse f b) == b)
inverse-inv-r (f , f-is-equiv) b = is-equiv.f-g f-is-equiv b

-- Equivalences are injective
equiv-inj : ∀ {i} {j} {A : Set i} {B : Set j} (f : A ≃ B) {x y : A}
  → (f ☆ x == f ☆ y → x == y)
equiv-inj f-eq {x} {y} p = let (f , g) = (fst f-eq , inverse f-eq) in
  x       =⟨ ! (inverse-inv-l f-eq x) ⟩
  g (f x) =⟨ ap g p ⟩
  g (f y) =⟨ inverse-inv-l f-eq y ⟩
  y ∎

-- Any contractible type is equivalent to the unit type
contr-equiv-Unit : ∀ {i j} {A : Type i} → (is-contr A → A ≃ Unit {j})
contr-equiv-Unit e = equiv (λ _ → tt) (λ _ → fst e) (λ _ → idp) (λ a → snd e a)
