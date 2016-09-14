{-# OPTIONS --without-K #-}

open import lib.Basics

module lib.types.Empty where

Empty-rec : ∀ {i} {A : Type i} → (Empty → A)
Empty-rec = Empty-elim

⊥-rec : ∀ {i} {A : Type i} → (⊥ → A)
⊥-rec = Empty-rec

abstract
  Empty-is-prop : is-prop Empty
  Empty-is-prop = Empty-elim

  Empty-is-set : is-set Empty
  Empty-is-set = raise-level -1 Empty-is-prop

  Empty-level = Empty-is-prop
  ⊥-is-prop = Empty-is-prop
  ⊥-is-set = Empty-is-set
  ⊥-level = Empty-level

negated-equiv-Empty : ∀ {i} (A : Type i) → (¬ A) → (Empty ≃ A)
negated-equiv-Empty A notA = equiv Empty-elim
                                   notA
                                   (λ a → Empty-elim {P = λ _ → Empty-elim (notA a) == a} (notA a))
                                   (Empty-elim {P = λ e → notA (Empty-elim e) == e})
