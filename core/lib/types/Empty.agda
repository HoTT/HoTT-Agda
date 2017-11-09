{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

module lib.types.Empty where

Empty-rec : ∀ {i} {A : Type i} → (Empty → A)
Empty-rec = Empty-elim

⊥-rec : ∀ {i} {A : Type i} → (⊥ → A)
⊥-rec = Empty-rec

Empty-is-prop : is-prop Empty
Empty-is-prop = has-level-in Empty-elim

instance
  Empty-level : {n : ℕ₋₂} → has-level (S n) Empty
  Empty-level = prop-has-level-S Empty-is-prop

Empty-is-set : is-set Empty
Empty-is-set = raise-level -1 Empty-is-prop

⊥-is-prop = Empty-is-prop
⊥-is-set = Empty-is-set
⊥-level = Empty-level
