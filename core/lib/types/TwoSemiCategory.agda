{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

module lib.types.TwoSemiCategory where

module _ {i j} {El : Type i} (Arr : El → El → Type j)
  (_ : ∀ x y → has-level 1 (Arr x y)) where

  record TwoSemiCategoryStructure : Type (lmax i j) where
    field
      comp : ∀ {x y z} → Arr x y → Arr y z → Arr x z
      assoc : ∀ {x y z w} (a : Arr x y) (b : Arr y z) (c : Arr z w)
        → comp (comp a b) c == comp a (comp b c)
      {- coherence -}
      pentagon-identity : ∀ {v w x y z} (a : Arr v w) (b : Arr w x) (c : Arr x y) (d : Arr y z)
        → assoc (comp a b) c d ◃∙
          assoc a b (comp c d) ◃∎
          =ₛ
          ap (λ s → comp s d) (assoc a b c) ◃∙
          assoc a (comp b c) d ◃∙
          ap (comp a) (assoc b c d) ◃∎

record TwoSemiCategory i j : Type (lsucc (lmax i j)) where
  constructor two-semi-category
  field
    El : Type i
    Arr : El → El → Type j
    Arr-level : ∀ x y → has-level 1 (Arr x y)
    two-semi-cat-struct : TwoSemiCategoryStructure Arr Arr-level

  open TwoSemiCategoryStructure two-semi-cat-struct public
