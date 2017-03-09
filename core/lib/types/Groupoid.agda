{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.TLevel
open import lib.types.Sigma
open import lib.types.Pi

module lib.types.Groupoid where

record GroupoidStructure {i j} {El : Type i} (Arr : El → El → Type j)
  (_ : ∀ x y → has-level 0 (Arr x y)) : Type (lmax i j) where
  field
    ident : ∀ {x} → Arr x x
    inv : ∀ {x y} → Arr x y → Arr y x
    comp : ∀ {x y z} → Arr x y → Arr y z → Arr x z
    unit-l : ∀ {x y} (a : Arr x y) → comp ident a == a
    assoc : ∀ {x y z w} (a : Arr x y) (b : Arr y z) (c : Arr z w)
              → comp (comp a b) c == comp a (comp b c)
    inv-l : ∀ {x y } (a : Arr x y) → (comp (inv a) a) == ident

  private
    infix 80 _⊙_
    _⊙_ = comp

  abstract
    inv-r  : ∀ {x y} (a : Arr x y) → a ⊙ inv a == ident
    inv-r a =
      a ⊙ inv a                           =⟨ ! $ unit-l (a ⊙ inv a) ⟩
      ident ⊙ (a ⊙ inv a)                 =⟨ ! $ inv-l (inv a) |in-ctx _⊙ (a ⊙ inv a) ⟩
      (inv (inv a) ⊙ inv a) ⊙ (a ⊙ inv a) =⟨ assoc (inv (inv a)) (inv a) (a ⊙ inv a) ⟩
      inv (inv a) ⊙ (inv a ⊙ (a ⊙ inv a)) =⟨ ! $ assoc (inv a) a (inv a) |in-ctx inv (inv a) ⊙_ ⟩
      inv (inv a) ⊙ ((inv a ⊙ a) ⊙ inv a) =⟨ inv-l a |in-ctx (λ h → inv (inv a) ⊙ (h ⊙ inv a)) ⟩
      inv (inv a) ⊙ (ident ⊙ inv a)       =⟨ unit-l (inv a) |in-ctx inv (inv a) ⊙_ ⟩
      inv (inv a) ⊙ inv a                 =⟨ inv-l (inv a) ⟩
      ident                               =∎

    unit-r : ∀ {x y} (a : Arr x y) → a ⊙ ident == a
    unit-r a =
      a ⊙ ident          =⟨ ! (inv-l a) |in-ctx a ⊙_ ⟩
      a ⊙ (inv a ⊙ a)    =⟨ ! $ assoc a (inv a) a ⟩
      (a ⊙ inv a) ⊙ a    =⟨ inv-r a |in-ctx _⊙ a ⟩
      ident ⊙ a          =⟨ unit-l a ⟩
      a                  =∎

record PreGroupoid i j : Type (lsucc (lmax i j)) where
  constructor groupoid
  field
    El : Type i
    Arr : El → El → Type j
    Arr-level : ∀ x y → has-level 0 (Arr x y)
    groupoid-struct : GroupoidStructure Arr Arr-level
