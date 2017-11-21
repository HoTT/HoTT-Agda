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
    
    (emloop g)
    loop'
    (λ _ _ → set-↓-has-all-paths-↓)
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
    (Ω^S-group 0 ⊙[ (EM₁ G.grp → EM₁ G.grp) , (λ x → x) ])
  mult-hom = record {f = f; pres-comp = pres-comp}
    where
    f = λ g → λ= (mult-loop g)

    pres-comp = λ g₁ g₂ →
      ap λ= (λ= (EM₁-elim
        {P = λ x → mult-loop (G.comp g₁ g₂) x
                == mult-loop g₁ x ∙ mult-loop g₂ x}
        (emloop-comp g₁ g₂)
        (λ _ → prop-has-all-paths-↓)
        (λ _ _ → set-↓-has-all-paths-↓)))
      ∙ ! (∙-λ= _ _)

  mult : EM₁ G.grp → EM₁ G.grp → EM₁ G.grp
  mult = EM₁-rec {C = EM₁ G.grp → EM₁ G.grp} (λ x → x) mult-hom

  H-⊙EM₁ : HSpaceStructure (⊙EM₁ G.grp)
  H-⊙EM₁ = from-alt-h-space $ record { μ = mult; unit-l = unit-l; unit-r = unit-r; coh = coh }
    where
    unit-l : (x : EM₁ G.grp) → mult embase x == x
    unit-l = EM₁-elim
      {P = λ x → mult embase x == x}
      idp
      (λ g → ↓-app=idf-in $ ∙'-unit-l (emloop g) ∙ (! (ap-idf (emloop g)))
                            ∙ ! (∙-unit-r (ap (mult embase) (emloop g))))
      (λ _ _ → set-↓-has-all-paths-↓)

    unit-r : (x : EM₁ G.grp) → mult x embase == x
    unit-r = EM₁-elim
      {P = λ x → mult x embase == x}
      idp
      (λ g → ↓-app=idf-in $
         idp ∙' emloop g
           =⟨ ∙'-unit-l (emloop g) ⟩
         emloop g
           =⟨ ! (app=-β (mult-loop g) embase) ⟩
         app= (λ= (mult-loop g)) embase
           =⟨ ! (EM₁Rec.emloop-β {C = EM₁ G.grp → EM₁ G.grp}
                   (λ x → x) mult-hom g)
              |in-ctx (λ w → app= w embase) ⟩
         app= (ap mult (emloop g)) embase
           =⟨ ∘-ap (λ f → f embase) mult (emloop g) ⟩
         ap (λ z → mult z embase) (emloop g)
           =⟨ ! (∙-unit-r (ap (λ z → mult z embase) (emloop g))) ⟩
         ap (λ z → mult z embase) (emloop g) ∙ idp ∎)
      (λ _ _ → set-↓-has-all-paths-↓)

    coh : unit-l embase == unit-r embase
    coh = idp

  open HSpaceStructure H-⊙EM₁
