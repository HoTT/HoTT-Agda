{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Truncation

module Homotopy.Pointed where

record pType (i : Level) : Set (suc i) where
  constructor _,_
  field
    ∣_∣ : Set i  -- \|
    ⋆ : ∣_∣  -- \*
open pType public

pType₀ : Set₁
pType₀ = pType zero

_→⋆_ : ∀ {i j} → (pType i → pType j → pType (max i j))
_→⋆_ A B = (Σ (∣ A ∣ → ∣ B ∣) (λ f → f (⋆ A) ≡ ⋆ B), ((λ _ → ⋆ B) , refl _))

τ⋆ : ∀ {i} → (ℕ₋₂ → pType i → pType i)
τ⋆ n (X , x) = (τ n X , proj x)

is-contr⋆ : ∀ {i} → (pType i → Set i)
is-contr⋆ (X , x) = is-contr X

_≃⋆_ : ∀ {i j} → (pType i → pType j → Set (max i j))
(X , x) ≃⋆ (Y , y) = Σ (X ≃ Y) (λ f → π₁ f x ≡ y)

id-equiv⋆ : ∀ {i} (X : pType i) → X ≃⋆ X
id-equiv⋆ (X , x) = (id-equiv X , refl x)

equiv-compose⋆ : ∀ {i j k} {A : pType i} {B : pType j} {C : pType k}
  → (A ≃⋆ B → B ≃⋆ C → A ≃⋆ C)
equiv-compose⋆ (f , pf) (g , pg) = (equiv-compose f g , (map (π₁ g) pf ∘ pg))

pType-eq-raw : ∀ {i} {X Y : pType i} (p : ∣ X ∣ ≡ ∣ Y ∣)
  (q : transport (λ X → X) p (⋆ X) ≡ ⋆ Y) → X ≡ Y
pType-eq-raw {i} {(X , x)} {(.X , .x)} (refl .X) (refl .x) = refl _

pType-eq : ∀ {i} {X Y : pType i} → (X ≃⋆ Y → X ≡ Y)
pType-eq (e , p) = pType-eq-raw (eq-to-path e) (trans-X-eq-to-path e _ ∘ p)
