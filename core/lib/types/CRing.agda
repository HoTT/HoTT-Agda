{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Group
open import lib.groups.Homomorphism

module lib.types.CRing where

-- 1-approximation of commutative rings without higher coherence conditions.
record CRingStructure {i} (El : Type i)
  : Type i where
  constructor ring-structure
  field
    add-group-struct : GroupStructure El

  open GroupStructure add-group-struct

  zero : El
  zero = ident

  add : El → El → El
  add = comp

  neg : El → El
  neg = inv

  field
    add-comm    : ∀ a b → add a b == add b a
    one         : El
    mult        : El → El → El
    mult-unit-l : ∀ a → mult one a == a
    mult-assoc  : ∀ a b c → mult (mult a b) c == mult a (mult b c)
    mult-comm   : ∀ a b → mult a b == mult b a
    distr-l : ∀ a b c → mult (add a b) c == add (mult a c) (mult b c)

  private
    infix 80 _⊕_
    _⊕_ = add
    infix 90 _⊗_
    _⊗_ = mult

  add-assoc : ∀ a b c → (a ⊕ b) ⊕ c == a ⊕ (b ⊕ c)
  add-assoc = assoc

  abstract
    mult-unit-r : ∀ a → a ⊗ one == a
    mult-unit-r a =
      a ⊗ one  =⟨ mult-comm a one ⟩
      one ⊗ a  =⟨ mult-unit-l a ⟩
      a        =∎

    distr-r : ∀ a b c → a ⊗ (b ⊕ c) == a ⊗ b ⊕ a ⊗ c
    distr-r a b c =
      a ⊗ (b ⊕ c)    =⟨ mult-comm a (add b c) ⟩
      (b ⊕ c) ⊗ a    =⟨ distr-l b c a ⟩
      b ⊗ a ⊕ c ⊗ a  =⟨ (mult-comm b a) |in-ctx (λ x → add x (mult c a)) ⟩
      a ⊗ b ⊕ c ⊗ a  =⟨ (mult-comm c a) |in-ctx (add (mult a b)) ⟩
      a ⊗ b ⊕ a ⊗ c  =∎

    mult-zero-l : ∀ a → zero ⊗ a == zero
    mult-zero-l a =
      cancel-l (zero ⊗ a) $
        zero ⊗ a ⊕ zero ⊗ a  =⟨ ! (distr-l zero zero a) ⟩
        (zero ⊕ zero) ⊗ a    =⟨ unit-l zero |in-ctx (λ x → x ⊗ a) ⟩
        zero ⊗ a             =⟨ ! (unit-r (zero ⊗ a)) ⟩
        zero ⊗ a ⊕ zero      =∎

    mult-zero-r : ∀ a → a ⊗ zero == zero
    mult-zero-r a =
      a ⊗ zero  =⟨ mult-comm a zero ⟩
      zero ⊗ a  =⟨ mult-zero-l a ⟩
      zero      =∎

record CRing i : Type (lsucc i) where
  constructor ring
  field
    El : Type i
    {{El-level}} : has-level 0 El
    ring-struct : CRingStructure El
  open CRingStructure ring-struct public

  add-group : Group i
  add-group = group El add-group-struct

  add-ab-group : AbGroup i
  add-ab-group = add-group , add-comm

  mult-hom : El → add-group →ᴳ add-group
  mult-hom g = group-hom (mult g) (distr-r g)

  mult-hom-zero : mult-hom zero == cst-hom
  mult-hom-zero = group-hom= (λ= mult-zero-l)

Ring₀ : Type (lsucc lzero)
Ring₀ = CRing lzero
