{-# OPTIONS --without-K #-}

module lib.Coproduct where

open import lib.Base

data Coprod {i j} (A : Type i) (B : Type j) : Type (max i j) where
  inl : A → Coprod A B
  inr : B → Coprod A B
