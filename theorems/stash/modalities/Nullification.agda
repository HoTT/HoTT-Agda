{-# OPTIONS --without-K --rewriting #-}

open import HoTT

open import Orthogonality
open import Modalities

module Nullification where

  module _ {ℓ} where

    private

      data #Nullify (X A : Type ℓ) : Type ℓ where
        #inj : A → #Nullify X A
        #apex : (X → #Nullify X A) → #Nullify X A

    _↯_ : (X A : Type ℓ) → Type ℓ
    X ↯ A = #Nullify X A

    inj : {X A : Type ℓ} → A → X ↯ A
    inj = #inj

    apex : {X A : Type ℓ} → (X → X ↯ A) → X ↯ A
    apex = #apex

    postulate
      apex-path : {X A : Type ℓ} (φ : X → X ↯ A) (x : X) → apex φ == φ x
      apex-cst : {X A : Type ℓ} (a♭ : X ↯ A) → apex (λ _ → a♭) == a♭
      apex-adj : {X A : Type ℓ} (a♭ : X ↯ A) → ap (Δ (X ↯ A) X) (apex-cst a♭) == λ= (apex-path (λ _ → a♭))

    module ↯-Elim {X A : Type ℓ} (P : X ↯ A → Type ℓ) (orth : ⟦ X ⊥ P ⟧ᵣ) (f₀ : Π A (P ∘ inj)) where

      f : Π (X ↯ A) P
      f (#inj a) = f₀ a
      f (#apex φ) = is-equiv.g (orth (#apex φ)) φ'

        where φ' : X → P (#apex φ)
              φ' x = transport! P (apex-path φ x) (f (φ x))

    module ↯-Rec {X A B : Type ℓ} (orth : ⟦ X ⊥ B ⟧ₒ) (f₀ : A → B) where

      f : X ↯ A → B
      f = ↯-Elim.f (λ _ → B) (λ _ → orth) f₀

  module _ {ℓ} where

    _≲_ : Type ℓ → Type ℓ → Type ℓ
    A ≲ X = is-contr (X ↯ A)

    ↯-is-local : {X A : Type ℓ} → ⟦ X ⊥ X ↯ A ⟧ₒ
    is-equiv.g ↯-is-local = apex
    is-equiv.f-g ↯-is-local α = λ= (apex-path α)
    is-equiv.g-f ↯-is-local = apex-cst
    is-equiv.adj ↯-is-local = apex-adj

  module _ {ℓ} (X A : Type ℓ) where

    SX↯A : Type ℓ
    SX↯A = (Suspension X) ↯ A

    SX↯A== : A → A → Type ℓ
    SX↯A== a₀ a₁ = Path {A = SX↯A} (inj a₀) (inj a₁)
    
    lemma : (a₀ a₁ : A) → ⟦ X ⊥ SX↯A== a₀ a₁ ⟧ₒ
    lemma a₀ a₁ = record { g = escape ; f-g = {!!} ; g-f = {!!} ; adj = {!!} }

      where escape : (X → SX↯A== a₀ a₁) → SX↯A== a₀ a₁
            escape α = ! (apex-path test north) ∙ apex-path test south

              where test : Suspension X → SX↯A
                    test = Suspension-rec (inj a₀) (inj a₁) α

    thm-to : (a₀ a₁ : A) → X ↯ (a₀ == a₁) → SX↯A== a₀ a₁
    thm-to a₀ a₁ = ↯-Rec.f (lemma a₀ a₁) (ap inj)

    -- Not sure if this is legit ...
    thm-from : (a₀ a₁ : A) → SX↯A== a₀ a₁ → X ↯ (a₀ == a₁)
    thm-from a₀ .a₀ idp = inj idp

  module _ {ℓ} (W B : Type ℓ) (X : B → Type ℓ) where

    -- Going to try to state Bousfield's lemmas here
    ΣW : Type ℓ
    ΣW = Suspension W
    
    -- The first lemma is simply closure under Σ-types
    lemma₁ : ⟦ W ⊥ B ⟧ₒ → ⟦ W ⊥ X ⟧ᵣ → ⟦ W ⊥ Σ B X ⟧ₒ
    lemma₁ = {!!}

    lemma₂ : ⟦ ΣW ⊥ Σ B X ⟧ₒ → ⟦ W ⊥ X ⟧ᵣ → ⟦ ΣW ⊥ B ⟧ₒ
    lemma₂ = {!!}
    
    lemma₃ : ⟦ W ⊥ Σ B X ⟧ₒ → ⟦ ΣW ⊥ B ⟧ₒ → ⟦ W ⊥ X ⟧ᵣ
    lemma₃ = {!!}


  module _ {ℓ} (X A B : Type ℓ) (f : A → B) where

    ΣX : Type ℓ
    ΣX = Suspension X

    thm : (b : B) → A ≲ X → B ≲ X → hfiber f b ≲ ΣX
    thm b α β = {!!}

  -- What's the next claim?  It's something like that, if I have a
  -- map f : A → B, then if A and B are X acyclic, the homotopy fiber
  -- of f is ΣX acyclic.

  module _ {ℓ} (X : Type ℓ) where

    join-proj : (Y A : Type ℓ) → (X * Y) ↯ A → Y ↯ A
    join-proj Y A = ↯-Rec.f (jn-ideal ↯-is-local) inj



