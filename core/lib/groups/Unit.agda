{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Group
open import lib.types.Unit
open import lib.groups.SubgroupProp
open import lib.groups.Homomorphism
open import lib.groups.Isomorphism
open import lib.groups.Lift

module lib.groups.Unit where

Unit-group-structure : GroupStructure Unit
Unit-group-structure = record
  { ident = unit
  ; inv = λ _ → unit
  ; comp = λ _ _ → unit
  ; unit-l = λ _ → idp
  ; assoc = λ _ _ _ → idp
  ; inv-l = λ _ → idp
  }

Unit-group : Group lzero
Unit-group = group _ Unit-group-structure

0ᴳ = Unit-group

abstract
  Unit-group-is-trivial : is-trivialᴳ Unit-group
  Unit-group-is-trivial = λ _ → idp

  iso-Unit-is-trivial : ∀ {i} {G : Group i} → G ≃ᴳ Unit-group → is-trivialᴳ G
  iso-Unit-is-trivial G-iso-0 = iso-preserves'-trivial G-iso-0 Unit-group-is-trivial

0ᴳ-is-trivial = Unit-group-is-trivial
iso-0ᴳ-is-trivial = iso-Unit-is-trivial

trivial-iso-Unit : ∀ {i} {G : Group i} → is-trivialᴳ G → G ≃ᴳ Unit-group
trivial-iso-Unit {G = G} G-triv = group-hom (λ _ → tt) (λ _ _ → idp) ,
  is-eq _ (λ _ → Group.ident G) (λ _ → idp) (λ _ → ! (G-triv _))

trivial-iso-0ᴳ = trivial-iso-Unit

{- the following should be replaced by [is-trivial] completely -}

abstract
  contr-iso-Unit : ∀ {i} (G : Group i) → is-contr (Group.El G) → G ≃ᴳ Unit-group
  contr-iso-Unit G pA = ≃-to-≃ᴳ (contr-equiv-Unit pA) (λ _ _ → idp)
contr-iso-0ᴳ = contr-iso-Unit

Unit-group-is-abelian : is-abelian 0ᴳ
Unit-group-is-abelian _ _ = idp

0ᴳ-is-abelian = Unit-group-is-abelian

Unit-abgroup : AbGroup₀
Unit-abgroup = Unit-group , Unit-group-is-abelian

0ᴳ-abgroup = Unit-abgroup

abstract
  hom₁-Unit-is-trivial : ∀ {i} (G : AbGroup i) → is-trivialᴳ (hom-group Unit-group G)
  hom₁-Unit-is-trivial G φ = group-hom= $ λ= λ _ → GroupHom.pres-ident φ

hom₁-0ᴳ-is-trivial = hom₁-Unit-is-trivial
