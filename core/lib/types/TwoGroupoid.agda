{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

module lib.types.TwoGroupoid where

record TwoGroupoidStructure {i j} {El : Type i} (Arr : El → El → Type j)
  (_ : ∀ x y → has-level 1 (Arr x y)) : Type (lmax i j) where
  field
    ident : ∀ {x} → Arr x x
    inv : ∀ {x y} → Arr x y → Arr y x
    comp : ∀ {x y z} → Arr x y → Arr y z → Arr x z
    unit-l : ∀ {x y} (a : Arr x y) → comp ident a == a
    unit-r : ∀ {x y} (a : Arr x y) → comp a ident == a
    assoc : ∀ {x y z w} (a : Arr x y) (b : Arr y z) (c : Arr z w)
              → comp (comp a b) c == comp a (comp b c)
    inv-l : ∀ {x y} (a : Arr x y) → (comp (inv a) a) == ident
    inv-r : ∀ {x y} (a : Arr x y) → (comp a (inv a)) == ident

    {- coherence -}
    triangle-identity : ∀ {x y z} (a : Arr x y) (b : Arr y z)
      → ap (λ s → comp s b) (unit-r a) == assoc a ident b ∙ ap (comp a) (unit-l b)

    pentagon-identity : ∀ {v w x y z} (a : Arr v w) (b : Arr w x) (c : Arr x y) (d : Arr y z)
      → assoc (comp a b) c d ∙ assoc a b (comp c d)
        == ap (λ s → comp s d) (assoc a b c) ∙ assoc a (comp b c) d ∙ ap (comp a) (assoc b c d)

    inv-coherence : ∀ {x y} (a : Arr x y)
      → ap (λ s → comp s a) (inv-r a) ∙ unit-l a
        == assoc a (inv a) a ∙ ap (comp a) (inv-l a) ∙ unit-r a

record PreTwoGroupoid i j : Type (lsucc (lmax i j)) where
  constructor groupoid
  field
    El : Type i
    Arr : El → El → Type j
    Arr-level : ∀ x y → has-level 1 (Arr x y)
    two-groupoid-struct : TwoGroupoidStructure Arr Arr-level
