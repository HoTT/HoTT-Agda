{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.types.TLevel
open import lib.types.Group
open import lib.types.LoopSpace
open import lib.groups.GroupProduct
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
    assoc = Ω^S-∙-assoc n;
    inv-l = Ω^S-!-inv-l n
    }

  Ω^'S-group-structure : GroupStructure (Ω^' (S n) X)
  Ω^'S-group-structure = record {
    ident = idp^' (S n);
    inv = Ω^'S-! n;
    comp = Ω^'S-∙ n;
    unit-l = Ω^'S-∙-unit-l n;
    assoc = Ω^'S-∙-assoc n;
    inv-l = Ω^'S-!-inv-l n
    }

  Ω^S-group : {{_ : has-level ⟨ S n ⟩ (de⊙ X)}} → Group i
  Ω^S-group = group
    (Ω^ (S n) X)
    -- TODO: make it find it automatically
    {{Ω^-level 0 (S n) X $
       transport (λ t → has-level t (de⊙ X)) (! (+2+0 ⟨ S n ⟩₋₂)) ⟨⟩}}
    Ω^S-group-structure

  Ω^'S-group : {{_ : has-level ⟨ S n ⟩ (de⊙ X)}} → Group i
  Ω^'S-group = group
    (Ω^' (S n) X)
    -- TODO: make it find it automatically
    {{Ω^'-is-set (S n) X ⟨⟩}}
    Ω^'S-group-structure

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

  Ω^'S-group-structure-fmap : X ⊙→ Y
    → GroupStructureHom (Ω^'S-group-structure n X) (Ω^'S-group-structure n Y)
  Ω^'S-group-structure-fmap F = group-structure-hom (Ω^'-fmap (S n) F) (Ω^'S-fmap-∙ n F)

  Ω^'S-group-structure-isemap : {F : X ⊙→ Y}
    → is-equiv (fst F) → is-equiv (GroupStructureHom.f (Ω^'S-group-structure-fmap F))
  Ω^'S-group-structure-isemap {F} F-is-equiv = Ω^'-isemap (S n) F F-is-equiv

  Ω^'S-group-structure-emap : X ⊙≃ Y
    → Ω^'S-group-structure n X ≃ᴳˢ Ω^'S-group-structure n Y
  Ω^'S-group-structure-emap (F , F-is-equiv) =
    Ω^'S-group-structure-fmap F , Ω^'S-group-structure-isemap F-is-equiv

module _ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  {{X-level : has-level ⟨ S n ⟩ (de⊙ X)}}
  {{Y-level : has-level ⟨ S n ⟩ (de⊙ Y)}}
  where

  Ω^S-group-fmap : X ⊙→ Y → Ω^S-group n X →ᴳ Ω^S-group n Y
  Ω^S-group-fmap = →ᴳˢ-to-→ᴳ ∘ Ω^S-group-structure-fmap n

  Ω^S-group-emap : X ⊙≃ Y → Ω^S-group n X ≃ᴳ Ω^S-group n Y
  Ω^S-group-emap = ≃ᴳˢ-to-≃ᴳ ∘ Ω^S-group-structure-emap n

  Ω^'S-group-fmap : X ⊙→ Y → Ω^'S-group n X →ᴳ Ω^'S-group n Y
  Ω^'S-group-fmap = →ᴳˢ-to-→ᴳ ∘ Ω^'S-group-structure-fmap n

  Ω^'S-group-emap : X ⊙≃ Y → Ω^'S-group n X ≃ᴳ Ω^'S-group n Y
  Ω^'S-group-emap = ≃ᴳˢ-to-≃ᴳ ∘ Ω^'S-group-structure-emap n

module _ {i j} where

  private
    Ω-group-structure-× : ∀ (X : Ptd i) (Y : Ptd j)
      → Ω^S-group-structure 0 (X ⊙× Y) ≃ᴳˢ Ω^S-group-structure 0 X ×ᴳˢ Ω^S-group-structure 0 Y
    Ω-group-structure-× X Y = ≃-to-≃ᴳˢ (Ω-× X Y) (Ω-×-∙ X Y)

  Ω^S-group-structure-× : ∀ (n : ℕ) (X : Ptd i) (Y : Ptd j)
    → Ω^S-group-structure n (X ⊙× Y) ≃ᴳˢ Ω^S-group-structure n X ×ᴳˢ Ω^S-group-structure n Y
  Ω^S-group-structure-× n X Y =
    Ω-group-structure-× (⊙Ω^ n X) (⊙Ω^ n Y) ∘eᴳˢ Ω^S-group-structure-emap 0 (⊙Ω^-× n X Y)

  Ω^'S-group-structure-× : ∀ (n : ℕ) (X : Ptd i) (Y : Ptd j)
    → Ω^'S-group-structure n (X ⊙× Y) ≃ᴳˢ Ω^'S-group-structure n X ×ᴳˢ Ω^'S-group-structure n Y
  Ω^'S-group-structure-× O X Y = Ω-group-structure-× X Y
  Ω^'S-group-structure-× (S n) X Y =
    Ω^'S-group-structure-× n (⊙Ω X) (⊙Ω Y) ∘eᴳˢ Ω^'S-group-structure-emap n (⊙Ω-× X Y)
