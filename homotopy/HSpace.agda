{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.HSpace where

record HSpaceStructure {i} (A : Type i) : Type i where
  constructor hSpaceStructure
  field
    e : A
    μ : A → A → A
    μe- : (a : A) → μ e a == a
    μ-e : (a : A) → μ a e == a

module ConnectedHSpace {i} (A : Type i) (c : is-connected ⟨0⟩ A)
  (hA : HSpaceStructure A) where

  open HSpaceStructure hA

  {-
  Given that [A] is 0-connected, to prove that each [μ a] is an equivalence we
  only need to prove that one of them is. But for [a] = [e], [μ a] is the 
  identity so we’re done.
  -}

  μ-is-equiv : (a : A) → is-equiv (μ a)
  μ-is-equiv = prop-over-connected {a = e} c
    (λ a → (is-equiv (μ a) , is-equiv-is-prop (μ a)))
    (transport! is-equiv (λ= μe-) (idf-is-equiv A))

  μ'-is-equiv : (a : A) → is-equiv (λ a' → μ a' a)
  μ'-is-equiv = prop-over-connected {a = e} c
    (λ a → (is-equiv (λ a' → μ a' a) , is-equiv-is-prop (λ a' → μ a' a)))
    (transport! is-equiv (λ= μ-e) (idf-is-equiv A))

  μ-equiv : A → A ≃ A
  μ-equiv a = (μ a , μ-is-equiv a)

  μ'-equiv : A → A ≃ A
  μ'-equiv a = ((λ a' → μ a' a) , μ'-is-equiv a)
