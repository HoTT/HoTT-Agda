{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Empty
open import lib.types.Group
open import lib.types.Word
open import lib.groups.GeneratedGroup
open import lib.groups.Homomorphism

module lib.groups.FreeGroup where

module FreeGroup {i} (A : Type i) where

  private
    module Gen = GeneratedGroup A empty-rel
  open Gen hiding (GenGroup) public

  FreeGroup : Group i
  FreeGroup = Gen.GenGroup

  module Freeness {j} (G : Group j) where

    private
      module G = Group G
      module HE = HomomorphismEquiv G

    extend-equiv : (A → G.El) ≃ (FreeGroup →ᴳ G)
    extend-equiv =
      HE.extend-equiv ∘e every-function-respects-empty-rel-equiv A G

    extend : (A → G.El) → (FreeGroup →ᴳ G)
    extend = –> extend-equiv

    extend-is-equiv : is-equiv extend
    extend-is-equiv = snd extend-equiv
