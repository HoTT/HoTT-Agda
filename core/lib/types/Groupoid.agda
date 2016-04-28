{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.types.TLevel
open import lib.types.Sigma
open import lib.types.Pi

module lib.types.Groupoid where

record GroupoidStructure {i j} {El : Type i} (Arr : El → El → Type j)
  (_ : ∀ x y → has-level ⟨0⟩ (Arr x y)) : Type (lmax i j) where
  field
    id : ∀ {x} → Arr x x
    inv : ∀ {x y} → Arr x y → Arr y x
    comp : ∀ {x y z} → Arr x y → Arr y z → Arr x z
    unit-l : ∀ {x y} (a : Arr x y) → comp id a == a
    unit-r : ∀ {x y} (a : Arr x y) → comp a id == a
    assoc   : ∀ {x y z w} (a : Arr x y) (b : Arr y z) (c : Arr z w)
              → comp (comp a b) c == comp a (comp b c)
    inv-r    : ∀ {x y} (a : Arr x y) → (comp a (inv a)) == id
    inv-l    : ∀ {x y } (a : Arr x y) → (comp (inv a) a) == id

record Groupoid {i j} : Type (lsucc (lmax i j)) where
  constructor groupoid
  field
    El : Type i
    Arr : El → El → Type j
    Arr-level : ∀ x y → has-level ⟨0⟩ (Arr x y)
    groupoid-struct : GroupoidStructure Arr Arr-level
