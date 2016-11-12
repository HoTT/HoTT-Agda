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
  ; unit-r = λ _ → idp
  ; assoc = λ _ _ _ → idp
  ; inv-r = λ _ → idp
  ; inv-l = λ _ → idp
  }

Unit-group : Group lzero
Unit-group = group _ Unit-is-set Unit-group-structure

0ᴳ = Unit-group

0ᴳ-is-trivial : is-trivialᴳ 0ᴳ
0ᴳ-is-trivial = λ _ → idp

iso-0ᴳ-is-trivial : ∀ {i} {G : Group i} → G ≃ᴳ 0ᴳ → is-trivialᴳ G
iso-0ᴳ-is-trivial G-iso-0 = iso-preserves'-trivial G-iso-0 0ᴳ-is-trivial

trivial-iso-0ᴳ : ∀ {i} {G : Group i} → is-trivialᴳ G → G ≃ᴳ 0ᴳ
trivial-iso-0ᴳ {G = G} G-triv = group-hom (λ _ → tt) (λ _ _ → idp) ,
  is-eq _ (λ _ → Group.ident G) (λ _ → idp) (λ _ → ! (G-triv _))

{- the following should be replaced by [is-trivial] completely -}

contr-iso-0ᴳ : ∀ {i} (G : Group i) → is-contr (Group.El G) → G ≃ᴳ 0ᴳ
contr-iso-0ᴳ G pA = ≃-to-≃ᴳ (contr-equiv-Unit pA) (λ _ _ → idp)

0ᴳ-hom-out-level : ∀ {i} {G : Group i}
  → is-contr (0ᴳ →ᴳ G)
0ᴳ-hom-out-level {G = G} =
  cst-hom , λ φ → group-hom= $ λ= λ _ → ! (GroupHom.pres-ident φ)

0ᴳ-hom-in-level : ∀ {i} {G : Group i}
  → is-contr (G →ᴳ 0ᴳ)
0ᴳ-hom-in-level {G = G} = cst-hom , λ φ → group-hom= $ λ= λ _ → idp
