{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.types.TLevel
open import lib.types.Sigma
open import lib.types.Pi

module lib.types.Groupoid where

record Groupoid {i j} {El : Type i} (Arr : El → El → Type j) : Type (lmax i j) where
  constructor groupoid
  field
    Arr-level : ∀ {x y} → has-level ⟨0⟩ (Arr x y)
    ident : ∀ {x} → Arr x x
    inv : ∀ {x y} → Arr x y → Arr y x
    comp : ∀ {x y z} → Arr x y → Arr y z → Arr x z
    unitl : ∀ {x y} (a : Arr x y) → comp ident a == a
    unitr : ∀ {x y} (a : Arr x y) → comp a ident == a
    assoc   : ∀ {x y z w} (a : Arr x y) (b : Arr y z) (c : Arr z w)
              → comp (comp a b) c == comp a (comp b c)
    invr    : ∀ {x y} (a : Arr x y) → (comp a (inv a)) == ident
    invl    : ∀ {x y } (a : Arr x y) → (comp (inv a) a) == ident
open Groupoid
