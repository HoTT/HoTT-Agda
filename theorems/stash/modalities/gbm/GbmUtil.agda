{-# OPTIONS --without-K --rewriting #-}

open import HoTT

open import stash.modalities.Modalities

module stash.modalities.gbm.GbmUtil where

  prop-lemma : ∀ {ℓ} {A : Type ℓ} {a₀ a₁ : A} (P : A → hProp ℓ)
               (p : a₀ == a₁) (x₀ : (fst ∘ P) a₀) (x₁ : (fst ∘ P) a₁) →
               x₀ == x₁ [ (fst ∘ P) ↓ p ]
  prop-lemma P idp x₀ x₁ = prop-has-all-paths (snd (P _)) x₀ x₁              

  pths-ovr-is-prop : ∀ {ℓ} {A : Type ℓ} {a₀ a₁ : A} (P : A → hProp ℓ)
                     (p : a₀ == a₁) (x₀ : (fst ∘ P) a₀) (x₁ : (fst ∘ P) a₁) →
                     is-prop (x₀ == x₁ [ (fst ∘ P) ↓ p ])
  pths-ovr-is-prop P idp x₀ x₁ = =-preserves-level (snd (P _))                             

  postulate
  
    map-equiv-hfiber : ∀ {i₀ i₁ j₀ j₁}
      {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
      (f₀ : A₀ → B₀) (f₁ : A₁ → B₁) (hA : A₀ → A₁) (hB : B₀ → B₁)
      (sq : CommSquare f₀ f₁ hA hB) (ise-hA : is-equiv hA) (ise-hB : is-equiv hB) →
      (b₀ : B₀) → hfiber f₀ b₀ ≃ hfiber f₁ (hB b₀)

  -- map-equiv-hfiber f₀ f₁ hA hB (comm-sqr α) ise-hA ise-hB b₀ =
  --   equiv to from {!!} {!!}

  --   where to : hfiber f₀ b₀ → hfiber f₁ (hB b₀)
  --         to (a₀ , idp) = hA a₀ , ! (α a₀)

  --         from : hfiber f₁ (hB b₀) → hfiber f₀ b₀
  --         from (a₁ , p) = (is-equiv.g ise-hA a₁) , {!!}
  

          

