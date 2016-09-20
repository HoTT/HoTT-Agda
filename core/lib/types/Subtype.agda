{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2

-- [Subtype] is defined in lib.NType.

module lib.types.Subtype where

infix 40 _⊆_
_⊆_ : ∀ {i j₁ j₂} {A : Type i} → SubtypeProp A j₁ → SubtypeProp A j₂
  → Type (lmax i (lmax j₁ j₂))
P₁ ⊆ P₂ = ∀ a → SubtypeProp.prop P₁ a → SubtypeProp.prop P₂ a

infix 80 _∘sub_
_∘sub_ : ∀ {i j k} {A : Type i} {B : Type j}
  → SubtypeProp B k → (A → B) → SubtypeProp A k
P ∘sub f = SubtypeProp.prop P ∘ f , SubtypeProp.level P ∘ f
