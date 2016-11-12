{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.HSpace

module homotopy.EM1HSpace where

module EM₁HSpace {i} (G : AbGroup i) where

  private
    module G = AbGroup G

  mult-loop : (g : G.El) (x : EM₁ G.grp) → x == x
  mult-loop g = EM₁-elim
    {P = λ x → x == x}
    (λ _ → =-preserves-level _ EM₁-level)
    (emloop g)
    loop'
    (λ _ _ → set-↓-has-all-paths-↓ (EM₁-level embase embase))
    where
    abstract
      loop' : (g' : G.El) → emloop' G.grp g == emloop g [ (λ x → x == x) ↓ emloop g' ]
      loop' g' = ↓-idf=idf-in' $
        emloop g ∙ emloop g'     =⟨ ! (emloop-comp' G.grp g g') ⟩
        emloop (G.comp g g')     =⟨ ap (emloop' G.grp) (G.comm g g') ⟩
        emloop (G.comp g' g)     =⟨ emloop-comp' G.grp g' g ⟩
        emloop g' ∙ emloop g     =⟨ ∙=∙' (emloop g') (emloop g) ⟩
        emloop g' ∙' emloop g    ∎

  mult-hom : GroupHom G.grp
    (Ω^S-group 0 ((EM₁ G.grp → EM₁ G.grp) , (λ x → x)) (Π-level (λ _ → EM₁-level)))
  mult-hom = record {f = f; pres-comp = pres-comp}
    where
    f = λ g → λ= (mult-loop g)

    pres-comp = λ g₁ g₂ →
      ap λ= (λ= (EM₁-elim
        {P = λ x → mult-loop (G.comp g₁ g₂) x
                == mult-loop g₁ x ∙ mult-loop g₂ x}
        (λ _ →  =-preserves-level _ (=-preserves-level _ EM₁-level))
        (emloop-comp g₁ g₂)
        (λ _ → prop-has-all-paths-↓ (EM₁-level _ _ _ _))
        (λ _ _ → set-↓-has-all-paths-↓ (=-preserves-level _ (EM₁-level _ _)))))
      ∙ ! (∙-λ= _ _)

  mult : EM₁ G.grp → EM₁ G.grp → EM₁ G.grp
  mult = EM₁-rec {C = EM₁ G.grp → EM₁ G.grp} (Π-level (λ _ → EM₁-level)) (λ x → x) mult-hom

  H-⊙EM₁ : HSpaceStructure (⊙EM₁ G.grp)
  H-⊙EM₁ = record { μ = mult; μ-e-l = μ-e-l; μ-e-r = μ-e-r; μ-coh = μ-coh }
    where
    μ-e-l : (x : EM₁ G.grp) → mult embase x == x
    μ-e-l = EM₁-elim
      {P = λ x → mult embase x == x}
      (λ _ → =-preserves-level 1 EM₁-level)
      idp
      (λ g → ↓-app=idf-in $ ∙'-unit-l (emloop g) ∙ (! (ap-idf (emloop g)))
                            ∙ ! (∙-unit-r (ap (mult embase) (emloop g))))
      (λ _ _ → set-↓-has-all-paths-↓ (EM₁-level _ _))

    μ-e-r : (x : EM₁ G.grp) → mult x embase == x
    μ-e-r = EM₁-elim
      {P = λ x → mult x embase == x}
      (λ _ → =-preserves-level 1 EM₁-level)
      idp
      (λ g → ↓-app=idf-in $
         idp ∙' emloop g
           =⟨ ∙'-unit-l (emloop g) ⟩
         emloop g
           =⟨ ! (app=-β (mult-loop g) embase) ⟩
         app= (λ= (mult-loop g)) embase
           =⟨ ! (EM₁Rec.emloop-β {C = EM₁ G.grp → EM₁ G.grp}
                   (Π-level (λ _ → EM₁-level)) (λ x → x) mult-hom g)
              |in-ctx (λ w → app= w embase) ⟩
         app= (ap mult (emloop g)) embase
           =⟨ ∘-ap (λ f → f embase) mult (emloop g) ⟩
         ap (λ z → mult z embase) (emloop g)
           =⟨ ! (∙-unit-r (ap (λ z → mult z embase) (emloop g))) ⟩
         ap (λ z → mult z embase) (emloop g) ∙ idp ∎)
      (λ _ _ → set-↓-has-all-paths-↓ (EM₁-level _ _))

    μ-coh : μ-e-l embase == μ-e-r embase
    μ-coh = idp

  open HSpaceStructure H-⊙EM₁
