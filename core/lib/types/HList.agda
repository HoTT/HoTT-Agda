{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.List

module lib.types.HList where

data HList {i} : List (Type i) → Type (lsucc i) where
  nil : HList nil
  _::_ : {A : Type i} {L : List (Type i)} → A → HList L → HList (A :: L)

hlist-curry-type : ∀ {i j} (L : List (Type i))
  (B : HList L → Type (lmax i j)) → Type (lmax i j)
hlist-curry-type nil B = B nil
hlist-curry-type {j = j} (A :: L) B =
  (x : A) → hlist-curry-type {j = j} L (λ xs → B (x :: xs))

hlist-curry : ∀ {i j} {L : List (Type i)} {B : HList L → Type (lmax i j)}
  (f : Π (HList L) B) → hlist-curry-type {j = j} L B
hlist-curry {L = nil} f = f nil
hlist-curry {L = A :: _} f = λ x → hlist-curry (λ xs → f (x :: xs))
