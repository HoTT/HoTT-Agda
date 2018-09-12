{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Group
open import lib.types.Word
open import lib.groups.GeneratedAbelianGroup
open import lib.groups.GeneratedGroup
open import lib.groups.GroupProduct
open import lib.groups.Homomorphism
open import lib.groups.Isomorphism

module lib.groups.FreeAbelianGroup {i} where

module FreeAbelianGroup (A : Type i) where

  private
    module Gen = GeneratedAbelianGroup A empty-rel
  open Gen hiding (GenAbGroup; module HomomorphismEquiv) public

  CommutativityRel : Rel (Word A) i
  CommutativityRel = AbGroupRel

  FormalSumRel : Rel (Word A) i
  FormalSumRel = QuotWordRel

  FormalSum : Type i
  FormalSum = QuotWord

  FreeGroup : Group i
  FreeGroup = Gen.GenGroup

  FreeAbGroup : AbGroup i
  FreeAbGroup = Gen.GenAbGroup

  module FreeAbGroup = AbGroup FreeAbGroup

  {- Universal Property -}
  module Freeness {j} (G : AbGroup j) where

    private
      module G = AbGroup G

    extend-equiv : (A → G.El) ≃ (FreeAbGroup.grp →ᴳ G.grp)
    extend-equiv =
      Gen.HomomorphismEquiv.extend-equiv G ∘e every-function-respects-empty-rel-equiv A G.grp

    extend : (A → G.El) → (FreeAbGroup.grp →ᴳ G.grp)
    extend = –> extend-equiv

    extend-is-equiv : is-equiv extend
    extend-is-equiv = snd extend-equiv

    extend-hom : Πᴳ A (λ _ → G.grp) →ᴳ hom-group FreeAbGroup.grp G
    extend-hom = record {M} where
      module M where
        f : (A → G.El) → (FreeAbGroup.grp →ᴳ G.grp)
        f = extend
        abstract
          pres-comp : preserves-comp (Group.comp (Πᴳ A (λ _ → G.grp))) (Group.comp (hom-group FreeAbGroup.grp G)) f
          pres-comp = λ f₁ f₂ → group-hom= $ λ= $
            QuotWord-elim
              (Word-extendᴳ-comp G f₁ f₂)
              (λ _ → prop-has-all-paths-↓)

    extend-iso : Πᴳ A (λ _ → G.grp) ≃ᴳ hom-group FreeAbGroup.grp G
    extend-iso = extend-hom , snd extend-equiv
