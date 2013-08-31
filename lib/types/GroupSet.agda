{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Pi
open import lib.types.Group

{-
    The definition of G-sets.  Thanks to Daniel Grayson.
-}

module lib.types.GroupSet {i} where

  -- The right group action with respect to the group [grp].
  record GsetStructure (grp : Group i) {j} (El : Type j)
    (_ : is-set El) : Type (lmax i j) where
    constructor gset-structure
    private
      module G = Group grp
      module GS = GroupStructure G.group-struct
    field
      act : El → G.El → El
      unit-r : ∀ x → act x GS.ident == x
      assoc : ∀ x g₁ g₂ → act (act x g₁) g₂ == act x (GS.comp g₁ g₂)

  -- The definition of a G-set.  A set [El] equipped with
  -- a right group action with respect to [grp].
  record Gset (grp : Group i) j : Type (lsucc (lmax i j)) where
    constructor gset
    field
      El : Type j
      El-level : is-set El
      gset-struct : GsetStructure grp El El-level
    open GsetStructure gset-struct public
    El-is-set = El-level

  -- A helper function to establish equivalence between two G-sets.
  -- Many data are just props and this function do the coversion for them
  -- for you.  You only need to show the non-trivial parts.
  module _ {grp : Group i} {j} {El : Type j} {El-level : is-set El} where
    private
      module G = Group grp
      module GS = GroupStructure G.group-struct
    open GsetStructure
    private
      gset-structure=' : ∀ {gss₁ gss₂ : GsetStructure grp El El-level}
        → (act= : act gss₁ == act gss₂)
        → unit-r gss₁ == unit-r gss₂
          [ (λ act → ∀ x → act x GS.ident == x) ↓ act= ]
        → assoc gss₁ == assoc gss₂
          [ (λ act → ∀ x g₁ g₂ →
              act (act x g₁) g₂ == act x (GS.comp g₁ g₂)) ↓ act= ]
        → gss₁ == gss₂
      gset-structure=' {gset-structure _ _ _} {gset-structure ._ ._ ._}
        idp idp idp = idp
  
    gset-structure= : ∀ {gss₁ gss₂ : GsetStructure grp El El-level}
      → (∀ x g → act gss₁ x g == act gss₂ x g)
      → gss₁ == gss₂
    gset-structure= act= = gset-structure='
      (λ= λ x → λ= λ g → act= x g)
      (prop-has-all-paths-↓ (Π-level λ _ → El-level _ _))
      (prop-has-all-paths-↓
        (Π-level λ _ → Π-level λ _ → Π-level λ _ → El-level _ _))

  module _ {grp : Group i} {j : ULevel} where
    private
      module G = Group grp
      module GS = GroupStructure G.group-struct
    open Gset {grp} {j}
    private
      gset='' : ∀ {gs₁ gs₂ : Gset grp j}
        → (El= : El gs₁ == El gs₂)
        → (El-level : El-level gs₁ == El-level gs₂ [ is-set ↓ El= ])
        → gset-struct gs₁ == gset-struct gs₂
          [ uncurry (GsetStructure grp) ↓ pair= El= El-level ]
        → gs₁ == gs₂
      gset='' {gset _ _ _} {gset ._ ._ ._} idp idp idp = idp

      gset=' : ∀ {gs₁ gs₂ : Gset grp j}
        → (El= : El gs₁ == El gs₂)
        → (El-level : El-level gs₁ == El-level gs₂ [ is-set ↓ El= ])
        → (∀ {x₁} {x₂} (p : x₁ == x₂ [ idf _ ↓ El= ]) g
            → act gs₁ x₁ g == act gs₂ x₂ g [ idf _ ↓ El= ])
        → gs₁ == gs₂
      gset=' {gset _ _ _} {gset ._ ._ _} idp idp act= =
        gset='' idp idp (gset-structure= λ x g → act= idp g)

    gset= : ∀ {gs₁ gs₂ : Gset grp j}
      → (El≃ : El gs₁ ≃ El gs₂)
      → (∀ {x₁} {x₂}
          → –> El≃ x₁ == x₂
          → ∀ g → –> El≃ (act gs₁ x₁ g) == act gs₂ x₂ g)
      → gs₁ == gs₂
    gset= El≃ act= =
      gset='
        (ua El≃)
        (prop-has-all-paths-↓ is-set-is-prop)
        (λ x= g → ↓-idf-ua-in El≃ $ act= (↓-idf-ua-out El≃ x=) g)
