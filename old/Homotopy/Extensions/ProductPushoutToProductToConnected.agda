{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Connected

module Homotopy.Extensions.ProductPushoutToProductToConnected
  {i j} {A A′ B B′ : Set i} (f : A → A′) (g : B → B′) (P : A′ → B′ → Set j)
  {n₁ n₂} ⦃ P-is-trunc : ∀ a′ b′ → is-truncated (n₁ +2+ n₂) (P a′ b′) ⦄
  (f-is-conn : has-connected-fibers n₁ f)
  (g-is-conn : has-connected-fibers n₂ g)
  (left* :  ∀ a′ b → P a′ (g b))
  (right* : ∀ a b′ → P (f a) b′)
  (glue* :  ∀ a b → left* (f a) b ≡ right* a (g b))
  where

  open import Homotopy.Truncation
  open import Homotopy.Extensions.ProductPushoutToProductToConnected.Magic

  {-
    -- The pushout diagram you should have in your mind.

    connected-extend-diag : pushout-diag i
    connected-extend-diag = record
      { A = A′ × B
      ; B = A × B′
      ; C = A × B
      ; f = λ{(a , b) → f a , b}
      ; g = λ{(a , b) → a , g b}
      }
  -}

  private
    -- The first part: The extension for a fixed [a] is n₁-truncated.
    extension₁ : ∀ a′ → Set (max i j)
    extension₁ a′ = extension g (P a′) (left* a′)

    extend-magic₁ : ∀ a′ → is-truncated n₁ (extension₁ a′)
    extend-magic₁ a′ = extension-is-truncated
      g g-is-conn (P a′) ⦃ P-is-trunc a′ ⦄ (left* a′)

    -- The second part: The extension of extensions is contractible.
    extension₂ : Set (max i j)
    extension₂ = extension f extension₁ (λ a → right* a , glue* a)

    extend-magic₂ : is-truncated ⟨-2⟩ extension₂
    extend-magic₂ = extension-is-truncated
      f f-is-conn extension₁ ⦃ extend-magic₁ ⦄ (λ a → right* a , glue* a)

    extend-magic₃ : extension₂
    extend-magic₃ = π₁ extend-magic₂

  abstract
    -- Get the buried function.
    connected-extend : ∀ a′ b′ → P a′ b′
    connected-extend a′ b′ = π₁ (π₁ extend-magic₃ a′) b′

    -- β rules
    connected-extend-β-left : ∀ a′ b → connected-extend a′ (g b) ≡ left* a′ b
    connected-extend-β-left a′ b = ! $ π₂ (π₁ extend-magic₃ a′) b

    connected-extend-β-right : ∀ a b′ → connected-extend (f a) b′ ≡ right* a b′
    connected-extend-β-right a b′ = ! $ happly (base-path (π₂ extend-magic₃ a)) b′
