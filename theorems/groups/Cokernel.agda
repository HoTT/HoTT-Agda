{-# OPTIONS --without-K --rewriting #-}

open import HoTT

-- an attempt to speed up [QuotGroup (im-nprop ...)]
-- which removes most intermediate constructions

module groups.Cokernel {i j}
  {G : Group i} {H : Group j}
  (φ : G →ᴳ H) (H-ab : is-abelian H) where

  --  G ---φ--→ᴳ H

  private
    module G = Group G
    module H = AbGroup (H , H-ab)
    module φ = GroupHom φ

  coker-rel : Rel H.El (lmax i j)
  coker-rel h₁ h₂ = Trunc -1 (hfiber φ.f (H.diff h₁ h₂))

  private
    coker-El : Type (lmax i j)
    coker-El = SetQuot coker-rel

  coker-struct : GroupStructure coker-El
  coker-struct = record {M} where
    module M where
      ident : coker-El
      ident = q[ H.ident ]

      inv : coker-El → coker-El
      inv = SetQuot-rec inv' inv-rel
        where
          inv' : H.El → coker-El
          inv' h = q[ H.inv h ]

          abstract
            inv-rel : ∀ {h₁ h₂} → coker-rel h₁ h₂ → inv' h₁ == inv' h₂
            inv-rel {h₁} {h₂} = Trunc-rec
              λ{(g , φg=h₁h₂⁻¹) → quot-rel
                [ G.inv g , φ.pres-inv g ∙ ap H.inv φg=h₁h₂⁻¹
                          ∙ H.inv-diff h₁ h₂ ∙ H.comm h₂ (H.inv h₁)
                          ∙ ap (H.comp (H.inv h₁)) (! (H.inv-inv h₂)) ]}

      comp : coker-El → coker-El → coker-El
      comp = SetQuot-rec comp' comp-rel where

        comp' : H.El → coker-El → coker-El
        comp' h₁ = SetQuot-rec comp'' comp'-rel where

          comp'' : H.El → coker-El
          comp'' h₂ = q[ H.comp h₁ h₂ ]

          abstract
            comp'-rel : ∀ {h₂ h₂'} → coker-rel h₂ h₂' → comp'' h₂ == comp'' h₂'
            comp'-rel {h₂} {h₂'} = Trunc-rec
              λ{(g , φg=h₂h₂'⁻¹) → quot-rel
                [ g , ! ( ap (H.comp (H.comp h₁ h₂)) (H.inv-comp h₁ h₂')
                        ∙ H.assoc h₁ h₂ (H.comp (H.inv h₂') (H.inv h₁))
                        ∙ ap (H.comp h₁) (! $ H.assoc h₂ (H.inv h₂') (H.inv h₁))
                        ∙ H.comm h₁ (H.comp (H.comp h₂ (H.inv h₂')) (H.inv h₁))
                        ∙ H.assoc (H.comp h₂ (H.inv h₂')) (H.inv h₁) h₁
                        ∙ ap2 H.comp (! φg=h₂h₂'⁻¹) (H.inv-l h₁)
                        ∙ H.unit-r (φ.f g) )]}

        abstract
          comp-rel : ∀ {h₁ h₁'} → coker-rel h₁ h₁' → comp' h₁ == comp' h₁'
          comp-rel {h₁} {h₁'} = Trunc-rec
            λ{(g , φg=h₁h₁'⁻¹) → λ= $ SetQuot-elim
              (λ h₂ → quot-rel
                  [ g , ! ( ap (H.comp (H.comp h₁ h₂)) (H.inv-comp h₁' h₂)
                          ∙ H.assoc h₁ h₂ (H.comp (H.inv h₂) (H.inv h₁'))
                          ∙ ap (H.comp h₁) ( ! (H.assoc h₂ (H.inv h₂) (H.inv h₁'))
                                          ∙ ap (λ h → H.comp h (H.inv h₁')) (H.inv-r h₂)
                                          ∙ H.unit-l (H.inv h₁'))
                          ∙ ! φg=h₁h₁'⁻¹ )])
              (λ _ → prop-has-all-paths-↓)}

      abstract
        unit-l : ∀ cok → comp ident cok == cok
        unit-l = SetQuot-elim
          (λ h → ap q[_] $ H.unit-l h)
          (λ _ → prop-has-all-paths-↓)

        assoc : ∀ cok₁ cok₂ cok₃ → comp (comp cok₁ cok₂) cok₃ == comp cok₁ (comp cok₂ cok₃)
        assoc = SetQuot-elim
          (λ h₁ → SetQuot-elim
            (λ h₂ → SetQuot-elim
              (λ h₃ → ap q[_] $ H.assoc h₁ h₂ h₃)
              (λ _ → prop-has-all-paths-↓))
            (λ _ → prop-has-all-paths-↓))
          (λ _ → prop-has-all-paths-↓)

        inv-l : ∀ cok → comp (inv cok) cok == ident
        inv-l = SetQuot-elim
          (λ h → ap q[_] $ H.inv-l h)
          (λ _ → prop-has-all-paths-↓)

  Coker : Group (lmax i j)
  Coker = group _ coker-struct

  module Coker = Group Coker

  {- correctness -}

  Coker-β : Coker ≃ᴳ QuotGroup (im-npropᴳ φ H-ab)
  Coker-β = ≃-to-≃ᴳ (ide _) to-pres-comp where
    abstract
      to-pres-comp : preserves-comp Coker.comp
        (QuotGroup.comp (im-npropᴳ φ H-ab)) (idf _)
      to-pres-comp = SetQuot-elim
        (λ _ → SetQuot-elim
          (λ _ → idp)
          (λ _ → prop-has-all-paths-↓))
        (λ _ → prop-has-all-paths-↓)
