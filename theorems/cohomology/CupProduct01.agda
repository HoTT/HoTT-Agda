{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane1 using (EM₁-level₁)
open import homotopy.EM1HSpace

module cohomology.CupProduct01 {i} (R : CRing i) where

  private
    module R = CRing R
  open R using () renaming (add-group to R₊)

  open EM₁HSpace R.add-ab-group renaming (mult to EM₁-mult)

  module CP₀₁ (g : R.El) where

    loop' : R.El → embase' R₊ == embase
    loop' g' = emloop (R.mult g g')

    comp' : (g₁' g₂' : R.El) → loop' (R.add g₁' g₂') == loop' g₁' ∙ loop' g₂'
    comp' g₁' g₂' = ap emloop (R.distr-r g g₁' g₂') ∙ emloop-comp _ _

    module Rec = EM₁Level₁Rec {G = R₊} {C = EM₁ R₊} {{EM₁-level₁ R₊}} embase (group-hom loop' comp')

    cp₀₁ : EM₁ R₊ → EM₁ R₊
    cp₀₁ = Rec.f

  open CP₀₁ public using (cp₀₁)

  module distr-l (g₁ g₂ : R.El) where

    f : EM₁ R₊ → EM₁ R₊
    f x = cp₀₁ (R.add g₁ g₂) x

    g : EM₁ R₊ → EM₁ R₊
    g x = EM₁-mult (cp₀₁ g₁ x) (cp₀₁ g₂ x)

    base' : f (embase' R₊) == g (embase' R₊)
    base' = idp

    loop' : (h : R.El) → base' == base' [ (λ x → f x == g x) ↓ emloop h ]
    loop' h = ↓-='-in {f = f} {g = g} {p = emloop h} {u = base'} {v = base'} $
      base' ∙' ap g (emloop h)
        =⟨ ∙'-unit-l (ap g (emloop h)) ⟩
      ap g (emloop h)
        =⟨ ! (ap2-diag (λ x y → EM₁-mult (cp₀₁ g₁ x) $ cp₀₁ g₂ y) (emloop h)) ⟩
      ap2 (λ x y → EM₁-mult (cp₀₁ g₁ x) $ cp₀₁ g₂ y) (emloop h) (emloop h)
        =⟨ ! (ap2-ap-l (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) (EM₁-mult ∘ cp₀₁ g₁) (emloop h) (emloop h)) ⟩
      ap2 (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) (ap (EM₁-mult ∘ cp₀₁ g₁) (emloop h)) (emloop h)
        =⟨ ap-∘ EM₁-mult (cp₀₁ g₁) (emloop h) |in-ctx (λ z → ap2 (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) z (emloop h)) ⟩
      ap2 (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) (ap EM₁-mult (ap (cp₀₁ g₁) (emloop h))) (emloop h)
        =⟨ CP₀₁.Rec.emloop-β g₁ h |in-ctx (λ z → ap2 (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) (ap EM₁-mult z) (emloop h)) ⟩
      ap2 (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) (ap EM₁-mult (emloop (R.mult g₁ h))) (emloop h)
        =⟨ MultRec.emloop-β (R.mult g₁ h) |in-ctx (λ z → ap2 (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) z (emloop h)) ⟩
      ap2 (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) (λ= (mult-loop (R.mult g₁ h))) (emloop h)
        =⟨ ap2-out (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) (λ= (mult-loop (R.mult g₁ h))) (emloop h) ⟩
      ap (λ (f : EM₁ R₊ → EM₁ R₊) → f embase) (λ= (mult-loop (R.mult g₁ h))) ∙ ap (cp₀₁ g₂) (emloop h)
        =⟨ app=-β (mult-loop (R.mult g₁ h)) embase |in-ctx (λ z → z ∙ ap (cp₀₁ g₂) (emloop h)) ⟩
      mult-loop (R.mult g₁ h) embase ∙ ap (cp₀₁ g₂) (emloop h)
        =⟨ idp ⟩
      emloop (R.mult g₁ h) ∙ ap (cp₀₁ g₂) (emloop h)
        =⟨ CP₀₁.Rec.emloop-β g₂ h |in-ctx (λ z → emloop (R.mult g₁ h) ∙ z) ⟩
      emloop (R.mult g₁ h) ∙ emloop (R.mult g₂ h)
        =⟨ ! (emloop-comp (R.mult g₁ h) (R.mult g₂ h)) ⟩
      emloop (R.add (R.mult g₁ h) (R.mult g₂ h))
        =⟨ ap emloop (! (R.distr-l g₁ g₂ h)) ⟩
      emloop (R.mult (R.add g₁ g₂) h)
        =⟨ ! (CP₀₁.Rec.emloop-β (R.add g₁ g₂) h) ⟩
      ap f (emloop h)
        =⟨ ! (∙-unit-r (ap f (emloop h))) ⟩
      ap f (emloop h) ∙ base' =∎

    abstract
      cp₀₁-distr-l : (g' : EM₁ R₊) → cp₀₁ (R.add g₁ g₂) g' == EM₁-mult (cp₀₁ g₁ g') (cp₀₁ g₂ g')
      cp₀₁-distr-l =
        EM₁-set-elim
          {P = λ x → f x == g x}
          {{λ x → has-level-apply (EM₁-level₁ R₊) _ _}}
          base' loop'

  open distr-l public using (cp₀₁-distr-l)
