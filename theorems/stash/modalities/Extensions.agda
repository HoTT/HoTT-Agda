{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Extensions where

  ExtensionOf : ∀ {ℓ} {A B : Type ℓ} (f : A → B) (P : B → Type ℓ) (φ : (a : A) → P (f a)) → Type ℓ
  ExtensionOf {A = A} {B = B} f P φ = Σ (Π B P) (λ ψ → (a : A) → ψ (f a) == φ a)

  syntax ExtensionOf f P φ = ⟨ P ⟩⟨ φ ↗ f ⟩

  path-extension : ∀ {ℓ} {A B : Type ℓ} {f : A → B}
                   {P : B → Type ℓ} {φ : (a : A) → P (f a)}
                   (e₀ e₁ : ⟨ P ⟩⟨ φ ↗ f ⟩) →
                   ⟨ (λ b → fst e₀ b == fst e₁ b) ⟩⟨ (λ a → snd e₀ a ∙ ! (snd e₁ a)) ↗ f ⟩ ≃ (e₀ == e₁)
  path-extension {f = f} (ψ₀ , ε₀) (ψ₁ , ε₁) = equiv to {!!} {!!} {!!}                   

    where to : ExtensionOf f (λ b → ψ₀ b == ψ₁ b) (λ a → ε₀ a ∙ ! (ε₁ a)) → (ψ₀ , ε₀) == (ψ₁ , ε₁)
          to (α , β) = pair= (λ= α) {!!}

          from : (ψ₀ , ε₀) == (ψ₁ , ε₁) → ExtensionOf f (λ b → ψ₀ b == ψ₁ b) (λ a → ε₀ a ∙ ! (ε₁ a))
          from p = {!!}
          
    --       from : (e₀ == e₁) → ⟨ (λ b → fst e₀ b == fst e₁ b) ⟩⟨ (λ a → snd e₀ a ∙ ! (snd e₁ a)) ↗ f ⟩
    --       from = {!!}
          
  -- Definition equiv_path_extension `{Funext} {A B : Type} {f : A -> B}
  --            {P : B -> Type} {d : forall x:A, P (f x)}
  --            (ext ext' : ExtensionAlong f P d)
  -- : (ExtensionAlong f
  --                   (fun y => pr1 ext y = pr1 ext' y)
  --                   (fun x => pr2 ext x @ (pr2 ext' x)^))
  --   <~> ext = ext'.
  
