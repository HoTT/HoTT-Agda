{-# OPTIONS --without-K #-}

open import lib.Basics

module lib.types.Empty where

⊥ = Empty

⊥-elim : ∀ {i} {P : ⊥ → Type i} → ((x : ⊥) → P x)
⊥-elim = Empty-elim

Empty-rec : ∀ {i} {A : Type i} → (Empty → A)
Empty-rec = Empty-elim

⊥-rec : ∀ {i} {A : Type i} → (⊥ → A)
⊥-rec = Empty-rec

Empty-is-prop : is-prop Empty
Empty-is-prop = Empty-elim

⊥-is-prop : is-prop ⊥
⊥-is-prop = Empty-is-prop
