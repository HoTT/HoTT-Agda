{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Orthogonality where

  Δ : ∀ {ℓ} (A B : Type ℓ) → A → (B → A)
  Δ A B a = λ _ → a

  ⟦_⊥_⟧ₒ : ∀ {ℓ} (X A : Type ℓ) → Type ℓ
  ⟦ X ⊥ A ⟧ₒ = is-equiv (Δ A X)
  
  ⟦_⊥_⟧ₗ : ∀ {ℓ} {I : Type ℓ} (X : I → Type ℓ) (A : Type ℓ) → Type ℓ
  ⟦_⊥_⟧ₗ {I = I} X A = (i : I) → ⟦ X i ⊥ A ⟧ₒ

  ⟦_⊥_⟧ᵣ : ∀ {ℓ} {I : Type ℓ} (X : Type ℓ) (A : I → Type ℓ) → Type ℓ
  ⟦_⊥_⟧ᵣ {I = I} X A = (i : I) → ⟦ X ⊥ A i ⟧ₒ

  ⟦_⊥_⟧ : ∀ {ℓ} {I J : Type ℓ} (X : I → Type ℓ) (A : J → Type ℓ) → Type ℓ
  ⟦_⊥_⟧ {ℓ} {I} {J} X A = (i : I) → (j : J) → ⟦ X i ⊥ A j ⟧ₒ

  cone-of : ∀ {ℓ} {A B : Type ℓ} → (A → B) → Type ℓ
  cone-of {ℓ} {A} {B} f = hfiber (Δ B A) f

  orth-to-contr-cones : ∀ {ℓ} {A B : Type ℓ} → ⟦ A ⊥ B ⟧ₒ → (f : A → B) → is-contr (cone-of f)
  orth-to-contr-cones is-orth f = equiv-is-contr-map is-orth f

  contr-cones-to-orth : ∀ {ℓ} {A B : Type ℓ} → (ε : (f : A → B) → is-contr (cone-of f)) → ⟦ A ⊥ B ⟧ₒ
  contr-cones-to-orth ε = contr-map-is-equiv ε

  -- module _ {ℓ} {X Y Z : Type ℓ} where

  --   jn-adj : (X * Y → Z) ≃ Σ (Y → Z) (λ φ → (x : X) → cone-of φ)
  --   jn-adj = equiv to from {!!} {!!}

  --     where to : (X * Y → Z) → Σ (Y → Z) (λ φ → (x : X) → cone-of φ)
  --           to φ = (φ ∘ right , (λ x → φ (left x) , λ= (λ y → ap φ (glue (x , y)))))

  --           from : Σ (Y → Z) (λ φ → (x : X) → cone-of φ) → (X * Y → Z)
  --           from (f , c) = PushoutRec.f (λ x → fst (c x)) f (λ { (x , y) → app= (snd (c x)) y })

  --   jn-ideal : ⟦ Y ⊥ Z ⟧ₒ → ⟦ X * Y ⊥ Z ⟧ₒ
  --   jn-ideal o = contr-cones-to-orth (λ φ → (is-equiv.g o (φ ∘ right) , {!!}) , {!!})

  module _ {ℓ} {I J : Type ℓ} where
  
    -- Pushout product (fiberwise join)
    _□_ : (X : I → Type ℓ) (Y : J → Type ℓ) → I × J → Type ℓ
    (X □ Y) (i , j) = X i * Y j

    -- Fiberwise diagonal (fibered version)
    ⟪_,_⟫ : (X : I → Type ℓ) (Y : J → Type ℓ) → (i : I) → (j : J) → (X i → Y j) → Type ℓ
    ⟪ X , Y ⟫ i j f = cone-of f

    -- Fiberwise diagonal (map version)
    ⟪_,_⟫₀ : (X : I → Type ℓ) (Y : J → Type ℓ) → (i : I) → (j : J) → Y j → (X i → Y j)
    ⟪ X , Y ⟫₀ a b y x = y

    fb-diag-orth : (X : I → Type ℓ) (Y : J → Type ℓ) → 
                   ⟦ X ⊥ Y ⟧ → (i : I) → (j : J) → (f : X i → Y j) → is-contr (⟪ X , Y ⟫ i j f)
    fb-diag-orth X Y ε i j f = orth-to-contr-cones (ε i j) f

  -- module _ {ℓ} {I J K : Type ℓ} where

  --   thm : (X : I → Type ℓ) (Y : J → Type ℓ) (Z : K → Type ℓ) 
  --         (i : I) (j : J) (k : K) (f : X i * Y j → Z k) → 
  --         ⟪ X □ Y , Z ⟫ (i , j) k f ≃ ⟪ X , ⟪ Y , Z ⟫ j k ⟫ i (λ y → f (right y)) (λ x → (f (left x)) , λ= (λ y → ap f (glue (x , y))))
  --   thm = {!!}



