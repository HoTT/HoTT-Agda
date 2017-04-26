{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module stash.modalities.Orthogonality where

  module _ {ℓ} where
  
    Δ : (A : Type ℓ) (X : Type ℓ) → A → (X → A)
    Δ A X = cst

    ⟦_⊥_⟧ : (X : Type ℓ) (A : Type ℓ) → Type _
    ⟦ X ⊥ A ⟧ = is-equiv (Δ A X)

    ⊤-orthogonal : (A : Type ℓ) → ⟦ Lift ⊤ ⊥ A ⟧
    ⊤-orthogonal A = record {
      g = λ φ → φ (lift unit) ;
      f-g = λ φ → λ= (λ { (lift unit) → idp }) ;
      g-f = λ a → idp ;
      adj = λ a → λ=-η idp }

    diag-equiv-lem : (A : Type ℓ) → is-equiv (Δ A A) → is-contr A
    diag-equiv-lem A e = is-equiv.g e (idf A) , (λ a → app= (is-equiv.f-g e (idf A)) a)
  
    self-ortho-contr : (A : Type ℓ) → ⟦ A ⊥ A ⟧ → is-contr A
    self-ortho-contr A ω = diag-equiv-lem A ω

    e-orth : {A B X : Type ℓ} → ⟦ A ⊥ X ⟧ → (A ≃ B) → ⟦ B ⊥ X ⟧
    e-orth {A} {B} {X} ω e = is-eq (Δ X B) g f-g g-f

      where g : (B → X) → X
            g φ = is-equiv.g ω (φ ∘ (fst e))

            f-g : (φ : B → X) → Δ X B (g φ) == φ
            f-g φ = λ= (λ b → app= (is-equiv.f-g ω (φ ∘ (fst e))) (<– e b) ∙ ap φ (<–-inv-r e b) )

            g-f : (x : X) → g (Δ X B x) == x
            g-f x = is-equiv.g-f ω x

    prod-to : {A B X : Type ℓ} → ⟦ A ⊥ X ⟧ → ⟦ B ⊥ X ⟧ → ⟦ A × B ⊥ X ⟧
    prod-to e f = is-eq _ (λ φ → is-equiv.g e (λ a → is-equiv.g f (λ b → φ (a , b))))
      (λ φ → λ= (λ { (a , b) → app= (is-equiv.f-g e (λ a → is-equiv.g f (λ b → φ (a , b)))) a ∙ app= (is-equiv.f-g f (λ b → φ (a , b))) b }))
      (λ x → ap (is-equiv.g e) (λ= (λ a → is-equiv.g-f f x)) ∙ is-equiv.g-f e x)

  -- Weak cellular inequalities
  module _ {ℓ} where
  
    _≻_ : Type ℓ → Type ℓ → Type _
    X ≻ A = (Y : Type ℓ) → ⟦ A ⊥ Y ⟧ → ⟦ X ⊥ Y ⟧

    equiv-≻ : {X Y : Type ℓ} {A : Type ℓ} → X ≻ A → X ≃ Y → Y ≻ A
    equiv-≻ {X} {Y} {A} ω e Z o = e-orth (ω Z o) e

    -- e-orth : {A B X : Type ℓ} → ⟦ A ⊥ X ⟧ → (A ≃ B) → ⟦ B ⊥ X ⟧

    ≻-trivial : (A : Type ℓ) → (Lift ⊤) ≻ A
    ≻-trivial A X ω = ⊤-orthogonal X
  
    ≻-reflexive : (A : Type ℓ) → A ≻ A
    ≻-reflexive A Y x = x

    ≻-trans : (A B C : Type ℓ) → A ≻ B → B ≻ C → A ≻ C
    ≻-trans A B C ω₀ ω₁ Y cy = ω₀ Y (ω₁ Y cy)
            
    ≻-⊤-is-contr : (A : Type ℓ) → A ≻ (Lift ⊤) → is-contr A
    ≻-⊤-is-contr A ω = self-ortho-contr A (ω A (⊤-orthogonal A))

    -- We jump a universe level, but its certainly convenient ...
    is-hyper-prop : Type ℓ → Type (lsucc ℓ)
    is-hyper-prop A = (X Y : Type ℓ) (f : X → Y) → X ≻ A → Y ≻ A → (y : Y) → hfiber f y ≻ A

    hyper-prop-kills-paths : (A : Type ℓ) → is-hyper-prop A → (a₀ a₁ : A) → a₀ == a₁ ≻ A
    hyper-prop-kills-paths A hp a₀ a₁ =
      equiv-≻ (hp (Lift ⊤) A (λ _ → a₀) (≻-trivial A) (≻-reflexive A) a₁)
      (equiv (λ { (lift unit , p) → p }) (λ p → (lift unit , p))
             (λ p → idp) (λ { (lift unit , p) → idp }))

  
