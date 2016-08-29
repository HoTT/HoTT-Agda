{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Group
open import lib.types.Unit
open import lib.groups.Homomorphisms
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

contr-iso-0ᴳ : ∀ {i} (G : Group i) → is-contr (Group.El G) → G ≃ᴳ 0ᴳ
contr-iso-0ᴳ G pA = ≃-to-≃ᴳ (contr-equiv-Unit pA) (λ _ _ → idp)

{-
contr-is-0ᴳ : ∀ {i} (G : Group i) → is-contr (Group.El G) → G == 0ᴳ
contr-is-0ᴳ G pA = uaᴳ $ contr-iso-0ᴳ G pA
-}

0ᴳ-hom-out-level : ∀ {i} {G : Group i}
  → is-contr (0ᴳ →ᴳ G)
0ᴳ-hom-out-level {G = G} =
  cst-hom , λ φ → group-hom= $ λ= λ _ → ! (GroupHom.pres-ident φ)

0ᴳ-hom-in-level : ∀ {i} {G : Group i}
  → is-contr (G →ᴳ 0ᴳ)
0ᴳ-hom-in-level {G = G} = cst-hom , λ φ → group-hom= $ λ= λ _ → idp
