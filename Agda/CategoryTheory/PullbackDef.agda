{-# OPTIONS --without-K #-}

open import Base

module CategoryTheory.PullbackDef {i j k} (A : Set i) (B : Set j) (C : Set k)
  (f : A → C) (g : B → C) where

record pullback : Set (max i (max j k)) where
  constructor _,_,_
  field
    a : A
    b : B
    h : f a ≡ g b
