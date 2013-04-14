{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.PathGroupoid

module lib.Equivalences where

record is-equiv {i j} {A : Type i} {B : Type j} (f : A → B) : Type (max i j)
  where
  field
    inv : B → A
    f-inv : (b : B) → f (inv b) == b
    inv-f : (a : A) → inv (f a) == a
    adj : (a : A) → ap f (inv-f a) == f-inv (f a)

_≃_ : ∀ {i j} (A : Type i) (B : Type j) → Type (max i j)
A ≃ B = Σ (A → B) is-equiv

Equiv = _≃_

homotopy-naturality-toid : ∀ {i} {A : Type i}
  (f : A -> A) (p : (x : A) → f x == x)
  {x y : A} (q : x == y) → p y == ! (ap f q) ∙ p x ∙ q
homotopy-naturality-toid f p idp = ! (∙-unit-l _)

equiv : ∀ {i j} {A : Type i} {B : Type j}
  (f : A → B) (g : B → A) (f-g : (b : B) → f (g b) == b)
  (g-f : (a : A) → g (f a) == a) → A ≃ B
equiv {A = A} {B = B} f g f-g g-f =
  (f , record {inv = g; f-inv = f-g'; inv-f = g-f; adj = adj}) where
    f-g' : (b : B) → f (g b) == b
    f-g' b = ! (ap (f ∘ g) (f-g b)) ∙ ap f (g-f (g b)) ∙ f-g b

    postulate
      adj : (a : A) → ap f (g-f a) == f-g' (f a)
--    adj a = {!homotopy-naturality-toid (f ∘ g) (λ a → ap f (g-f a)) (f-g (f a))!}
