{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Pi
open import lib.types.Group

{-
    The definition of G-sets.  Thanks to Daniel Grayson.
-}

module lib.types.GroupSet {i} where

  -- The right group action with respect to the group [grp].
  record GroupSetStructure (grp : Group i) {j} (El : Type j)
    (_ : is-set El) : Type (lmax i j) where
    constructor groupset-structure
    private
      module G = Group grp
      module GS = GroupStructure G.group-struct
    field
      act : El → G.El → El
      unit-r : ∀ x → act x GS.ident == x
      assoc : ∀ x g₁ g₂ → act (act x g₁) g₂ == act x (GS.comp g₁ g₂)

  -- The definition of a G-set.  A set [El] equipped with
  -- a right group action with respect to [grp].
  record GroupSet (grp : Group i) j : Type (lsucc (lmax i j)) where
    constructor groupset
    field
      El : Type j
      El-level : is-set El
      grpset-struct : GroupSetStructure grp El El-level
    open GroupSetStructure grpset-struct public
    El-is-set = El-level

  -- A helper function to establish equivalence between two G-sets.
  -- Many data are just props and this function do the coversion for them
  -- for you.  You only need to show the non-trivial parts.
  module _ {grp : Group i} {j} {El : Type j} {El-level : is-set El} where
    private
      module G = Group grp
      module GS = GroupStructure G.group-struct
    open GroupSetStructure
    private
      groupset-structure=' : ∀ {gss₁ gss₂ : GroupSetStructure grp El El-level}
        → (act= : act gss₁ == act gss₂)
        → unit-r gss₁ == unit-r gss₂
          [ (λ act → ∀ x → act x GS.ident == x) ↓ act= ]
        → assoc gss₁ == assoc gss₂
          [ (λ act → ∀ x g₁ g₂ →
              act (act x g₁) g₂ == act x (GS.comp g₁ g₂)) ↓ act= ]
        → gss₁ == gss₂
      groupset-structure=' {groupset-structure _ _ _} {groupset-structure ._ ._ ._}
        idp idp idp = idp

    groupset-structure= : ∀ {gss₁ gss₂ : GroupSetStructure grp El El-level}
      → (∀ x g → act gss₁ x g == act gss₂ x g)
      → gss₁ == gss₂
    groupset-structure= act= = groupset-structure='
      (λ= λ x → λ= λ g → act= x g)
      (prop-has-all-paths-↓ (Π-level λ _ → El-level _ _))
      (prop-has-all-paths-↓
        (Π-level λ _ → Π-level λ _ → Π-level λ _ → El-level _ _))

  module _ {grp : Group i} {j : ULevel} where
    private
      module G = Group grp
      module GS = GroupStructure G.group-struct
    open GroupSet {grp} {j}
    private
      groupset='' : ∀ {gs₁ gs₂ : GroupSet grp j}
        → (El= : El gs₁ == El gs₂)
        → (El-level : El-level gs₁ == El-level gs₂ [ is-set ↓ El= ])
        → grpset-struct gs₁ == grpset-struct gs₂
          [ uncurry (GroupSetStructure grp) ↓ pair= El= El-level ]
        → gs₁ == gs₂
      groupset='' {groupset _ _ _} {groupset ._ ._ ._} idp idp idp = idp

      groupset=' : ∀ {gs₁ gs₂ : GroupSet grp j}
        → (El= : El gs₁ == El gs₂)
        → (El-level : El-level gs₁ == El-level gs₂ [ is-set ↓ El= ])
        → (∀ {x₁} {x₂} (p : x₁ == x₂ [ idf _ ↓ El= ]) g
            → act gs₁ x₁ g == act gs₂ x₂ g [ idf _ ↓ El= ])
        → gs₁ == gs₂
      groupset=' {groupset _ _ _} {groupset ._ ._ _} idp idp act= =
        groupset='' idp idp (groupset-structure= λ x g → act= idp g)

    groupset= : ∀ {gs₁ gs₂ : GroupSet grp j}
      → (El≃ : El gs₁ ≃ El gs₂)
      → (∀ {x₁} {x₂}
          → –> El≃ x₁ == x₂
          → ∀ g → –> El≃ (act gs₁ x₁ g) == act gs₂ x₂ g)
      → gs₁ == gs₂
    groupset= El≃ act= =
      groupset='
        (ua El≃)
        (prop-has-all-paths-↓ is-set-is-prop)
        (λ x= g → ↓-idf-ua-in El≃ $ act= (↓-idf-ua-out El≃ x=) g)

  -- The GroupSet homomorphism.
  record GroupSetHom {grp : Group i} {j}
    (gset₁ gset₂ : GroupSet grp j) : Type (lmax i j) where
    constructor groupset-hom
    open GroupSet
    field
      f : El gset₁ → El gset₂
      pres-act : ∀ g x → f (act gset₁ x g) == act gset₂ (f x) g

  private
    groupset-hom=' : ∀ {grp : Group i} {j} {gset₁ gset₂ : GroupSet grp j}
      {gsh₁ gsh₂ : GroupSetHom gset₁ gset₂}
      → (f= : GroupSetHom.f gsh₁ == GroupSetHom.f gsh₂)
      → (GroupSetHom.pres-act gsh₁ == GroupSetHom.pres-act gsh₂
        [ (λ f → ∀ g x → f (GroupSet.act gset₁ x g) == GroupSet.act gset₂ (f x) g) ↓ f= ] )
      → gsh₁ == gsh₂
    groupset-hom=' idp idp = idp

  groupset-hom= : ∀ {grp : Group i} {j} {gset₁ gset₂ : GroupSet grp j}
    {gsh₁ gsh₂ : GroupSetHom gset₁ gset₂}
    → GroupSetHom.f gsh₁ ∼ GroupSetHom.f gsh₂
    → gsh₁ == gsh₂
  groupset-hom= {gset₂ = gset₂} f= =
    groupset-hom='
      (λ= f=)
      (prop-has-all-paths-↓ $
        Π-level λ _ → Π-level λ _ → GroupSet.El-level gset₂ _ _)

  group-to-group-set : ∀ (grp : Group i) → GroupSet grp i
  group-to-group-set grp = record {
    El = G.El;
    El-level = G.El-level;
    grpset-struct = record {
      act = G.comp;
      unit-r = G.unit-r;
      assoc = G.assoc}}
    where module G = Group grp
