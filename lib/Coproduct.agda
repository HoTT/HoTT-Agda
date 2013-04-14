{-# OPTIONS --without-K #-}

module lib.Coproduct where

open import lib.Base

data Coprod {i j} (A : Type i) (B : Type j) : Type (max i j) where
  inl : A → Coprod A B
  inr : B → Coprod A B

match_withl_withr_ : ∀ {i j k} {A : Type i} {B : Type j}
  {C : Coprod A B → Type k}
  (x : Coprod A B) (l : (a : A) → C (inl a)) (r : (b : B) → C (inr b)) → C x
match (inl a) withl l withr r = l a
match (inr b) withl l withr r = r b
