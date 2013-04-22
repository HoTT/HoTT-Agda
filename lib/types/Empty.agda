{-# OPTIONS --without-K #-}

open import lib.Basics

module lib.types.Empty where

Empty = ⊥

⊥-elim : ∀ {i} {P : ⊥ → Type i} → ((x : ⊥) → P x)
⊥-elim ()

⊥-is-prop : is-prop ⊥
⊥-is-prop = ⊥-elim
