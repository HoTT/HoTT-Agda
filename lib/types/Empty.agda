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

negated-equiv-Empty : ∀ {i} (A : Type i) → (¬ A) → (Empty ≃ A)
negated-equiv-Empty A notA = equiv Empty-elim
                                   notA
                                   (λ a → Empty-elim {P = λ _ → Empty-elim (notA a) == a} (notA a))
                                   (Empty-elim {P = λ e → notA (Empty-elim e) == e})
