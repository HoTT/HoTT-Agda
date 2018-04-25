{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EM1HSpace
open import homotopy.EilenbergMacLane1 using (EM₁-level₁)

module homotopy.EM1HSpaceAssoc where

module EM₁HSpaceAssoc {i} (G : AbGroup i) where

  private
    module G = AbGroup G
  open EM₁HSpace G

  mult-loop-mult : (g : G.El) (y z : EM₁ G.grp)
    → mult-loop g (mult y z) == ap (λ x' → mult x' z) (mult-loop g y)
  mult-loop-mult g y z =
    EM₁-prop-elim {P = λ y → mult-loop g (mult y z) == ap (λ x' → mult x' z) (mult-loop g y)}
                  {{λ y → has-level-apply (has-level-apply (EM₁-level₁ G.grp) _ _) _ _}}
                  base' y
    where
    base' : mult-loop g (mult embase z) == ap (λ x' → mult x' z) (mult-loop g embase)
    base' =
      mult-loop g z
        =⟨ ! (app=-β (mult-loop g) z) ⟩
      app= (λ= (mult-loop g)) z
        =⟨ ap (λ s → app= s z) (! (MultRec.emloop-β g)) ⟩
      app= (ap mult (emloop g)) z
        =⟨ ∘-ap (λ f → f z) mult (emloop g) ⟩
      ap (λ x' → mult x' z) (emloop g) =∎

  H-⊙EM₁-assoc : (x y z : EM₁ G.grp) → mult (mult x y) z == mult x (mult y z)
  H-⊙EM₁-assoc x y z =
    EM₁-set-elim {P = λ x → mult (mult x y) z == mult x (mult y z)}
                 {{λ x → has-level-apply (EM₁-level₁ G.grp) _ _}}
                 idp
                 comp'
                 x
    where
    comp' : (g : G.El) → idp == idp [ (λ x → mult (mult x y) z == mult x (mult y z)) ↓ emloop g ]
    comp' g =
      ↓-='-in $
      idp ∙' ap (λ x → mult x (mult y z)) (emloop g)
        =⟨ ∙'-unit-l _ ⟩
      ap (λ x → mult x (mult y z)) (emloop g)
        =⟨ ap-∘ (λ f → f (mult y z)) mult (emloop g) ⟩
      app= (ap mult (emloop g)) (mult y z)
        =⟨ ap (λ s → app= s (mult y z)) (MultRec.emloop-β g) ⟩
      app= (λ= (mult-loop g)) (mult y z)
        =⟨ app=-β (mult-loop g) (mult y z) ⟩
      mult-loop g (mult y z)
        =⟨ mult-loop-mult g y z ⟩
      ap (λ x' → mult x' z) (mult-loop g y)
        =⟨ ap (ap (λ x' → mult x' z)) (! (app=-β (mult-loop g) y)) ⟩
      ap (λ x' → mult x' z) (app= (λ= (mult-loop g)) y)
        =⟨ ∘-ap (λ x' → mult x' z) (λ f → f y) (λ= (mult-loop g)) ⟩
      ap (λ f → mult (f y) z) (λ= (mult-loop g))
        =⟨ ap (ap (λ f → mult (f y) z)) (! (MultRec.emloop-β g)) ⟩
      ap (λ f → mult (f y) z) (ap mult (emloop g))
        =⟨ ∘-ap (λ f → mult (f y) z) mult (emloop g) ⟩
      ap (λ x → mult (mult x y) z) (emloop g)
        =⟨ ! (∙-unit-r _) ⟩
      ap (λ x → mult (mult x y) z) (emloop g) ∙ idp =∎
