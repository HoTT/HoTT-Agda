{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane

module cohomology.CupProduct.OnEM.Higher {i} {j} (G : AbGroup i) (H : AbGroup j) where

open import cohomology.CupProduct.OnEM.Definition G H

private
  module G = AbGroup G
  module H = AbGroup H
  module G⊗H = TensorProduct G H
open EMExplicit G⊗H.abgroup

cp₁₁-embase-r : (x : EM₁ G.grp) → cp₁₁ x embase == [ north ]₂
cp₁₁-embase-r = M.f
  where
  module M =
    EM₁Level₂PathConstElim G.grp {C = EM 2} {{Trunc-level {n = 2}}}
      (λ x → cp₁₁ x embase) [ north ]₂
      idp
      (λ g → vert-degen-square (ap-cp₁₁-embase g))
      (λ g₁ g₂ →
        vert-degen-square (ap-cp₁₁-embase (G.comp g₁ g₂))
          =⟨ ap vert-degen-square $
             =ₛ-out (ap-cp₁₁-embase-coh g₁ g₂) ∙
             ! (∙-assoc (ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂))
                        (ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂))
                        (ap2 _∙_ (ap-cp₁₁-embase g₁) (ap-cp₁₁-embase g₂))) ⟩
        vert-degen-square
          ((ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ∙
            ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂)) ∙
           ap2 _∙_ (ap-cp₁₁-embase g₁) (ap-cp₁₁-embase g₂))
          =⟨ ! $ vert-degen-square-∙v⊡
                   (ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ∙
                    ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂))
                   (ap2 _∙_ (ap-cp₁₁-embase g₁) (ap-cp₁₁-embase g₂)) ⟩
        (ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ∙
         ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂)) ∙v⊡
        vert-degen-square (ap2 _∙_ (ap-cp₁₁-embase g₁) (ap-cp₁₁-embase g₂))
          =⟨ ap ((ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ∙
                  ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂)) ∙v⊡_) $
             ! (vert-degen-square-⊡h (ap-cp₁₁-embase g₁) (ap-cp₁₁-embase g₂)) ⟩
        (ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ∙
         ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂)) ∙v⊡
        (vert-degen-square (ap-cp₁₁-embase g₁) ⊡h
         vert-degen-square (ap-cp₁₁-embase g₂)) =∎)

module ∧-cp₁₁-Rec =
  SmashRec {X = ⊙EM₁ G.grp} {Y = ⊙EM₁ H.grp} {C = EM 2}
           cp₁₁
           [ north ]₂ [ north ]₂
           cp₁₁-embase-r
           (λ y → idp)

∧-cp₁₁ : ⊙EM₁ G.grp ∧ ⊙EM₁ H.grp → EM 2
∧-cp₁₁ = ∧-cp₁₁-Rec.f
