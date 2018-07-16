{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.HSpace
open import homotopy.EilenbergMacLane1 using (EM₁-level₁)

module homotopy.EM1HSpace where

module EM₁HSpace {i} (G : AbGroup i) where

  private
    module G = AbGroup G

  mult-loop' : G.El → (x : EM₁ G.grp) → x == x
  mult-loop' g = EM₁-set-elim
    {P = λ x → x == x}
    {{λ x → has-level-apply (EM₁-level₁ G.grp) x x}}
    (emloop g)
    loop'
    where
    abstract
      loop' : (g' : G.El) → emloop' G.grp g == emloop g [ (λ x → x == x) ↓ emloop g' ]
      loop' g' = ↓-idf=idf-in' $
        emloop g ∙ emloop g'     =⟨ ! (emloop-comp' G.grp g g') ⟩
        emloop (G.comp g g')     =⟨ ap (emloop' G.grp) (G.comm g g') ⟩
        emloop (G.comp g' g)     =⟨ emloop-comp' G.grp g' g ⟩
        emloop g' ∙ emloop g     =⟨ ∙=∙' (emloop g') (emloop g) ⟩
        emloop g' ∙' emloop g    ∎

  mult-loop : G.El → idf (EM₁ G.grp) == idf (EM₁ G.grp)
  mult-loop g = λ= (mult-loop' g)

  private
    EM₁-endo-Ω-group : Group i
    EM₁-endo-Ω-group = Ω^S-group 0 ⊙[ (EM₁ G.grp → EM₁ G.grp) , (λ x → x) ]

    mult-hom : GroupHom G.grp EM₁-endo-Ω-group
    mult-hom = record {f = mult-loop; pres-comp = pres-comp}
      where
      abstract
        pres-comp' : (g₁ g₂ : G.El) (x : EM₁ G.grp) →
          mult-loop' (G.comp g₁ g₂) x == mult-loop' g₁ x ∙ mult-loop' g₂ x
        pres-comp' g₁ g₂ =
          EM₁-prop-elim
            {P = λ x → mult-loop' (G.comp g₁ g₂) x == mult-loop' g₁ x ∙ mult-loop' g₂ x}
            {{λ x → has-level-apply (has-level-apply (EM₁-level₁ G.grp) _ _) _ _}}
            (emloop-comp g₁ g₂)

        pres-comp : (g₁ g₂ : G.El)
          → mult-loop (G.comp g₁ g₂) ==
            Group.comp EM₁-endo-Ω-group (mult-loop g₁) (mult-loop g₂)
        pres-comp g₁ g₂ =
          ap λ= (λ= (pres-comp' g₁ g₂)) ∙
          =ₛ-out (λ=-∙ (mult-loop' g₁) (mult-loop' g₂))

    module MultRec = EM₁Level₁Rec {G = G.grp} {C = EM₁ G.grp → EM₁ G.grp} (λ x → x) mult-hom

  abstract
    mult : EM₁ G.grp → EM₁ G.grp → EM₁ G.grp
    mult = MultRec.f

    mult-embase-β : mult embase ↦ (λ x → x)
    mult-embase-β = MultRec.embase-β
    {-# REWRITE mult-embase-β #-}

    mult-emloop-β : ∀ g → ap mult (emloop g) == mult-loop g
    mult-emloop-β = MultRec.emloop-β

  H-⊙EM₁ : HSpaceStructure (⊙EM₁ G.grp)
  H-⊙EM₁ = from-alt-h-space $ record { μ = mult; unit-l = unit-l; unit-r = unit-r; coh = coh }
    where
    unit-l : (x : EM₁ G.grp) → mult embase x == x
    unit-l = EM₁-set-elim
      {P = λ x → mult embase x == x}
      {{λ x → has-level-apply (EM₁-level₁ G.grp) (mult embase x) x}}
      idp
      (λ g → ↓-app=idf-in $ ∙'-unit-l (emloop g) ∙ (! (ap-idf (emloop g)))
                            ∙ ! (∙-unit-r (ap (mult embase) (emloop g))))

    unit-r : (x : EM₁ G.grp) → mult x embase == x
    unit-r = EM₁-set-elim
      {P = λ x → mult x embase == x}
      {{λ x → has-level-apply (EM₁-level₁ G.grp) (mult x embase) x}}
      idp
      (λ g → ↓-app=idf-in $
         idp ∙' emloop g
           =⟨ ∙'-unit-l (emloop g) ⟩
         emloop g
           =⟨ ! (app=-β (mult-loop' g) embase) ⟩
         app= (mult-loop g) embase
           =⟨ ! (mult-emloop-β g) |in-ctx (λ w → app= w embase) ⟩
         app= (ap mult (emloop g)) embase
           =⟨ ∘-ap (λ f → f embase) mult (emloop g) ⟩
         ap (λ z → mult z embase) (emloop g)
           =⟨ ! (∙-unit-r (ap (λ z → mult z embase) (emloop g))) ⟩
         ap (λ z → mult z embase) (emloop g) ∙ idp ∎)

    coh : unit-l embase == unit-r embase
    coh = idp

  open HSpaceStructure H-⊙EM₁
