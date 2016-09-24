{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.TLevel
open import lib.types.Group
open import lib.types.LoopSpace
open import lib.groups.Homomorphism
open import lib.groups.Isomorphism

module lib.groups.LoopSpace where

{- A loop space is a pregroup, and a group if it has the right level -}
module _ {i} (n : ℕ) (X : Ptd i) where

  Ω^S-group-structure : GroupStructure (Ω^ (S n) X)
  Ω^S-group-structure = record {
    ident = idp^ (S n);
    inv = Ω^S-! n;
    comp = Ω^S-∙ n;
    unit-l = Ω^S-∙-unit-l n;
    unit-r = Ω^S-∙-unit-r n;
    assoc = Ω^S-∙-assoc n;
    inv-r = Ω^S-!-inv-r n;
    inv-l = Ω^S-!-inv-l n
    }

  Ω^S-group : has-level ⟨ S n ⟩ (fst X) → Group i
  Ω^S-group pX = group
    (Ω^ (S n) X)
    (Ω^-level 0 (S n) X $
       transport (λ t → has-level t (fst X)) (! (+2+0 ⟨ S n ⟩₋₂)) pX)
    Ω^S-group-structure

module _ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j} where
  Ω^S-group-structure-fmap : X ⊙→ Y
    → GroupStructureHom (Ω^S-group-structure n X) (Ω^S-group-structure n Y)  
  Ω^S-group-structure-fmap F = group-structure-hom (Ω^-fmap (S n) F) (Ω^S-fmap-∙ n F)

  Ω^S-group-structure-isemap : {F : X ⊙→ Y}
    → is-equiv (fst F) → is-equiv (GroupStructureHom.f (Ω^S-group-structure-fmap F))
  Ω^S-group-structure-isemap {F} F-is-equiv = Ω^-isemap (S n) F F-is-equiv

  Ω^S-group-structure-emap : X ⊙≃ Y
    → Ω^S-group-structure n X ≃ᴳˢ Ω^S-group-structure n Y
  Ω^S-group-structure-emap (F , F-is-equiv) =
    Ω^S-group-structure-fmap F , Ω^S-group-structure-isemap F-is-equiv

module _ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  (X-level : has-level ⟨ S n ⟩ (fst X))
  (Y-level : has-level ⟨ S n ⟩ (fst Y))
  where

  Ω^S-group-fmap : X ⊙→ Y → Ω^S-group n X X-level →ᴳ Ω^S-group n Y Y-level
  Ω^S-group-fmap = →ᴳˢ-to-→ᴳ ∘ Ω^S-group-structure-fmap n

  Ω^S-group-emap : X ⊙≃ Y → Ω^S-group n X X-level ≃ᴳ Ω^S-group n Y Y-level
  Ω^S-group-emap = ≃ᴳˢ-to-≃ᴳ ∘ Ω^S-group-structure-emap n
