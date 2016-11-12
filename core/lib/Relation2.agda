{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Coproduct
open import lib.types.Empty
open import lib.types.Pi

module lib.Relation2 where

module _ {i} {P : Type i} where

  Dec-level : ∀ {n} → has-level (S n) P → has-level (S n) (Dec P)
  Dec-level pP (inl p₁) (inl p₂) =
    equiv-preserves-level (inl=inl-equiv p₁ p₂ ⁻¹) (pP p₁ p₂)
  Dec-level pP (inl p) (inr ¬p) = ⊥-rec $ ¬p p
  Dec-level pP (inr ¬p) (inl p) = ⊥-rec $ ¬p p
  Dec-level {n} pP (inr ¬p₁) (inr ¬p₂) =
    equiv-preserves-level (inr=inr-equiv ¬p₁ ¬p₂ ⁻¹)
      (prop-has-level-S ¬-is-prop ¬p₁ ¬p₂)
