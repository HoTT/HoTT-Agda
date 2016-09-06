{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Group
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Truncation
open import lib.types.SetQuotient
open import lib.groups.Homomorphisms
open import lib.groups.PropSubgroup

module lib.groups.PropNormalSubgroup where

record induces-normal-subgroup {i j} (G : Group i) (P : Group.El G → Type j)
  : Type (lmax i j) where
  private
    module G = Group G
  field
    ind-subgrp : induces-subgroup G P
  open induces-subgroup ind-subgrp public
  field
    cong : ∀ g₁ {g₂} → P g₂ → P (G.cong g₁ g₂)
  abstract
    comm : ∀ g₁ g₂ → P (G.comp g₁ g₂) → P (G.comp g₂ g₁)
    comm g₁ g₂ pg₁g₂ = transport P
      ( ap (λ g → G.comp g (G.inv g₂)) (! (G.assoc g₂ g₁ g₂))
      ∙ G.assoc (G.comp g₂ g₁) g₂ (G.inv g₂)
      ∙ ap (G.comp (G.comp g₂ g₁)) (G.inv-r g₂)
      ∙ G.unit-r _)
      (cong g₂ pg₁g₂)
    {- NOT USED
    uncong : ∀ g₁ g₂ → P (G.cong g₁ g₂) → P g₂
    uncong g₁ g₂ pg₁g₂ = transport P path (cong (G.inv g₁) pg₁g₂) where
      path : G.cong (G.inv g₁) (G.cong g₁ g₂) == g₂
      path = ! (G.cong-comp-l (G.inv g₁) g₁ g₂) ∙ ap (λ g → G.cong g g₂) (G.inv-l g₁) ∙ G.cong-unit-l g₂
    -}
