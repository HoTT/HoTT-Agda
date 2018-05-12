{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane
open import homotopy.EilenbergMacLane1 using (EM₁-level₁)
open import homotopy.EM1HSpace
open import homotopy.EM1HSpaceAssoc

module cohomology.CupProduct11 {i} (R : CRing i) where

  open import cohomology.CupProduct01 R

  private
    module R = CRing R
  open R using () renaming (add-group to R₊)
  open EM₁HSpaceAssoc R.add-ab-group renaming (mult to EM₁-mult; eq' to Pi2HSusp-eq'; comp to Pi2HSusp-comp)

  open EMExplicit R.add-ab-group

  module CP₁₁ where

    {-
    base'' : EM₁ R₊ → Susp (EM₁ R₊)
    base'' _ = north' (EM₁ R₊)

    base' : EM₁ R₊ → EM 2
    base' _ = pt (⊙EM 2)

    e₁ : Ω (⊙EM 2) ≃ Trunc 1 (north' (EM₁ R₊) == north)
    e₁ = =ₜ-equiv [ north' (EM₁ R₊) ] [ north' (EM₁ R₊) ]

    e₂ : Trunc 1 (north' (EM₁ R₊) == north) ≃ EM₁ R₊
    e₂ = Pi2HSusp-eq'

    ee : Ω (⊙EM 2) ≃ EM₁ R₊
    ee = e₂ ∘e e₁

    module _ (g : R.El) where

      loop'= : base' ∼ base'
      loop'= x = <– ee (cp₀₁ g x)

      loop' : base' == base'
      loop' = λ= loop'=

    module _ (g₁ g₂ : R.El) where

      comp'= : (x : EM₁ R₊) → loop'= (R.add g₂ g₁) x == loop'= g₁ x ∙ loop'= g₂ x
      comp'= x =
        loop'= (R.add g₂ g₁) x
          =⟨ ap (<– ee) (cp₀₁-distr-l g₂ g₁ x) ⟩
        <– ee (μ (cp₀₁ g₂ x) (cp₀₁ g₁ x))
          =⟨ ap (<– e₁) (Pi2HSusp-comp (cp₀₁ g₂ x) (cp₀₁ g₁ x)) ⟩
        <– e₁ ((<– e₂ (cp₀₁ g₁ x)) ∙₁ (<– e₂ (cp₀₁ g₂ x)))
          =⟨ <–-=ₜ-equiv-pres-∙ₜ {x = [ north ]} {y = [ north ]} {z = [ north ]}
                            (<– e₂ (cp₀₁ g₁ x)) (<– e₂ (cp₀₁ g₂ x)) ⟩
        loop'= g₁ x ∙ loop'= g₂ x =∎

      comp' : loop' (R.add g₁ g₂) == loop' g₁ ∙ loop' g₂
      comp' =
        loop' (R.add g₁ g₂)
          =⟨ ap loop' (R.add-comm g₁ g₂) ⟩
        loop' (R.add g₂ g₁)
          =⟨ ap λ= (λ= comp'=) ⟩
        λ= (λ x → loop'= g₁ x ∙ loop'= g₂ x)
          =⟨ ! (∙-λ= (loop'= g₁) (loop'= g₂)) ⟩
        loop' g₁ ∙ loop' g₂ =∎

    module _ (g₁ g₂ g₃ : R.El) where

      coh' : comp' (R.add g₁ g₂) g₃ ∙ ap (λ l → l ∙ loop' g₃) (comp' g₁ g₂) ∙ ∙-assoc (loop' g₁) (loop' g₂) (loop' g₃) ==
             ap loop' (R.add-assoc g₁ g₂ g₃) ∙ comp' g₁ (R.add g₂ g₃) ∙ ap (λ l → loop' g₁ ∙ l) (comp' g₂ g₃)
      coh' = {!!}
    -}

    cp₁₁ : EM₁ R₊ → EM₁ R₊ → EM 2
    cp₁₁ =
      EM₁-rec
        {C = EM₁ R₊ → EM 2}
        ?
