{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.HSpace

module homotopy.EM1HSpace where

module EM₁HSpace {i} (A : Group i) (A-abelian : is-abelian A) where

  module A = Group A
  open EM₁ A

  mult-loop : (g : A.El) (x : EM₁) → x == x
  mult-loop g = EM₁-elim
    {P = λ x → x == x}
    (λ _ → =-preserves-level _ emlevel)
    (emloop g)
    loop'
    (λ _ _ → set-↓-has-all-paths-↓ (emlevel embase embase))
    where
    abstract
      loop' : (g' : A.El) → emloop g == emloop g [ (λ x → x == x) ↓ emloop g' ]
      loop' g' = ↓-idf=idf-in $
        emloop g ∙ emloop g'     =⟨ ! (emloop-comp g g') ⟩
        emloop (A.comp g g')      =⟨ ap emloop (A-abelian g g') ⟩
        emloop (A.comp g' g)      =⟨ emloop-comp g' g ⟩
        emloop g' ∙ emloop g     =⟨ ∙=∙' (emloop g') (emloop g) ⟩
        emloop g' ∙' emloop g    ∎

  mult-hom : GroupHom A
    (Ω^S-group 0 ((EM₁ → EM₁) , (λ x → x)) (Π-level (λ _ → emlevel)))
  mult-hom = record {f = f; pres-comp = pres-comp}
    where
    f = λ g → λ= (mult-loop g)

    pres-comp = λ g₁ g₂ →
      ap λ= (λ= (EM₁-elim
        {P = λ x → mult-loop (A.comp g₁ g₂) x
                == mult-loop g₁ x ∙ mult-loop g₂ x}
        (λ _ →  =-preserves-level _ (=-preserves-level _ emlevel))
        (emloop-comp g₁ g₂)
        (λ _ → prop-has-all-paths-↓ (emlevel _ _ _ _))
        (λ _ _ → set-↓-has-all-paths-↓ (=-preserves-level _ (emlevel _ _)))))
      ∙ ! (∙-λ= _ _)

  mult : EM₁ → EM₁ → EM₁
  mult = EM₁-rec {C = EM₁ → EM₁} (Π-level (λ _ → emlevel)) (λ x → x) mult-hom

  H-⊙EM₁ : HSpaceStructure ⊙EM₁
  H-⊙EM₁ = record { μ = mult; μ-e-l = μ-e-l; μ-e-r = μ-e-r; μ-coh = μ-coh }
    where
    μ-e-l : (x : EM₁) → mult embase x == x
    μ-e-l = EM₁-elim
      {P = λ x → mult embase x == x}
      (λ _ → =-preserves-level 1 emlevel)
      idp
      (λ g → ↓-app=idf-in $ ∙'-unit-l (emloop g) ∙ (! (ap-idf (emloop g)))
                            ∙ ! (∙-unit-r (ap (mult embase) (emloop g))))
      (λ _ _ → set-↓-has-all-paths-↓ (emlevel _ _))

    μ-e-r : (x : EM₁) → mult x embase == x
    μ-e-r = EM₁-elim
      {P = λ x → mult x embase == x}
      (λ _ → =-preserves-level 1 emlevel)
      idp
      (λ g → ↓-app=idf-in $
         idp ∙' emloop g
           =⟨ ∙'-unit-l (emloop g) ⟩
         emloop g
           =⟨ ! (app=-β (mult-loop g) embase) ⟩
         app= (λ= (mult-loop g)) embase
           =⟨ ! (EM₁Rec.emloop-β {C = EM₁ → EM₁}
                   (Π-level (λ _ → emlevel)) (λ x → x) mult-hom g)
              |in-ctx (λ w → app= w embase) ⟩
         app= (ap mult (emloop g)) embase
           =⟨ ∘-ap (λ f → f embase) mult (emloop g) ⟩
         ap (λ z → mult z embase) (emloop g)
           =⟨ ! (∙-unit-r (ap (λ z → mult z embase) (emloop g))) ⟩
         ap (λ z → mult z embase) (emloop g) ∙ idp ∎)
      (λ _ _ → set-↓-has-all-paths-↓ (emlevel _ _))

    μ-coh : μ-e-l embase == μ-e-r embase
    μ-coh = idp

  open HSpaceStructure H-⊙EM₁
