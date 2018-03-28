{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Group

module lib.types.CRing where

-- 1-approximation of commutative rings without higher coherence conditions.
record CRingStructure {i} (El : Type i)
  : Type i where
  constructor ring-structure
  field
    add-group-struct : GroupStructure El
    add-comm    : ∀ a b → GroupStructure.comp add-group-struct a b == GroupStructure.comp add-group-struct b a
    one         : El
    mult        : El → El → El
    mult-unit-l : ∀ a → mult one a == a
    mult-assoc  : ∀ a b c → mult (mult a b) c == mult a (mult b c)
    mult-comm   : ∀ a b → mult a b == mult b a
    distr-l     : ∀ a b c → mult (GroupStructure.comp add-group-struct a b) c == GroupStructure.comp add-group-struct (mult a c) (mult b c)
  open GroupStructure add-group-struct

  add : El → El → El
  add = comp

  abstract
    mult-unit-r : ∀ a → mult a one == a
    mult-unit-r a =
      mult a one  =⟨ mult-comm a one ⟩
      mult one a  =⟨ mult-unit-l a ⟩
      a           =∎

  distr-r : ∀ a b c → mult a (add b c) == add (mult a b) (mult a c)
  distr-r a b c =
    mult a (add b c)           =⟨ mult-comm a (add b c) ⟩
    mult (add b c) a           =⟨ distr-l b c a ⟩
    add (mult b a) (mult c a)  =⟨ (mult-comm b a) |in-ctx (λ x → add x (mult c a)) ⟩
    add (mult a b) (mult c a)  =⟨ (mult-comm c a) |in-ctx (add (mult a b)) ⟩
    add (mult a b) (mult a c)  =∎

record CRing i : Type (lsucc i) where
  constructor ring
  field
    El : Type i
    {{El-level}} : has-level 0 El
    ring-struct : CRingStructure El
  open CRingStructure ring-struct public

Ring₀ : Type (lsucc lzero)
Ring₀ = CRing lzero
