{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Modality
open import lib.types.Truncation

module lib.modalities.Truncation where

Trunc-modality : ∀ {i} n → Modality i
Trunc-modality n = record {
  is-local = has-level n;
  is-local-is-prop = has-level-is-prop;
  ◯ = Trunc n;
  ◯-is-local = Trunc-level;
  η = [_];
  ◯-elim = λ f → Trunc-elim {{f}};
  ◯-elim-β = λ _ _ _ → idp;
  ◯-=-is-local = λ _ _ → =-preserves-level Trunc-level}
