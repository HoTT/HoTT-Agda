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
  ; unitl = λ _ → idp
  ; unitr = λ _ → idp
  ; assoc = λ _ _ _ → idp
  ; invr = λ _ → idp
  ; invl = λ _ → idp
  }

Unit-Group : Group lzero
Unit-Group = group _ Unit-is-set Unit-group-structure

LiftUnit-Group : ∀ {i} → Group i
LiftUnit-Group = Lift-Group Unit-Group

0ᴳ = LiftUnit-Group

contr-is-0ᴳ : ∀ {i} (G : Group i) → is-contr (Group.El G) → G == 0ᴳ
contr-is-0ᴳ G pA = group-ua
  (group-hom (λ _ → lift unit) (λ _ _ → idp) , snd (contr-equiv-LiftUnit pA))

0ᴳ-hom-out-level : ∀ {i j} {G : Group i}
  → is-contr (0ᴳ {j} →ᴳ G)
0ᴳ-hom-out-level {G = G} =
  (cst-hom ,
   λ φ → hom= _ _ (λ= (λ {(lift unit) → ! (GroupHom.pres-ident φ)})))

0ᴳ-hom-in-level : ∀ {i j} {G : Group i}
  → is-contr (G →ᴳ 0ᴳ {j})
0ᴳ-hom-in-level {G = G} =
  (cst-hom , λ φ → hom= _ _ (λ= (λ _ → idp)))
