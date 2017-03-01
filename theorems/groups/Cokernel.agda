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
      inv = SetQuot-rec SetQuot-level inv' inv-rel
        where
          inv' : H.El → coker-El
          inv' h = q[ H.inv h ]

          abstract
            inv-rel : ∀ {h₁ h₂} → coker-rel h₁ h₂ → inv' h₁ == inv' h₂
            inv-rel {h₁} {h₂} = Trunc-rec (SetQuot-level _ _)
              λ{(g , φg=h₁h₂⁻¹) → quot-rel
                [ G.inv g , φ.pres-inv g ∙ ap H.inv φg=h₁h₂⁻¹
                          ∙ H.inv-diff h₁ h₂ ∙ H.comm h₂ (H.inv h₁)
                          ∙ ap (H.comp (H.inv h₁)) (! (H.inv-inv h₂)) ]}

      comp : coker-El → coker-El → coker-El
      comp = SetQuot-rec level comp' comp-rel where
        abstract
          level : is-set (coker-El → coker-El)
          level = →-is-set SetQuot-level

        comp' : H.El → coker-El → coker-El
        comp' h₁ = SetQuot-rec SetQuot-level comp'' comp'-rel where

          comp'' : H.El → coker-El
          comp'' h₂ = q[ H.comp h₁ h₂ ]

          abstract
            comp'-rel : ∀ {h₂ h₂'} → coker-rel h₂ h₂' → comp'' h₂ == comp'' h₂'
            comp'-rel {h₂} {h₂'} = Trunc-rec (SetQuot-level _ _)
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
          comp-rel {h₁} {h₁'} = Trunc-rec (level _ _)
            λ{(g , φg=h₁h₁'⁻¹) → λ= $ SetQuot-elim (λ _ → =-preserves-set SetQuot-level)
              (λ h₂ → quot-rel
                  [ g , ! ( ap (H.comp (H.comp h₁ h₂)) (H.inv-comp h₁' h₂)
                          ∙ H.assoc h₁ h₂ (H.comp (H.inv h₂) (H.inv h₁'))
                          ∙ ap (H.comp h₁) ( ! (H.assoc h₂ (H.inv h₂) (H.inv h₁'))
                                          ∙ ap (λ h → H.comp h (H.inv h₁')) (H.inv-r h₂)
                                          ∙ H.unit-l (H.inv h₁'))
                          ∙ ! φg=h₁h₁'⁻¹ )])
              (λ _ → prop-has-all-paths-↓ (SetQuot-level _ _))}

      abstract
        unit-l : ∀ h → comp ident h == h
        unit-l = SetQuot-elim
          (λ _ → =-preserves-set SetQuot-level)
          (λ h → ap q[_] $ H.unit-l h)
          (λ _ → prop-has-all-paths-↓ (SetQuot-level _ _))

        unit-r : ∀ h → comp h ident == h
        unit-r = SetQuot-elim
          (λ _ → =-preserves-set SetQuot-level)
          (λ h → ap q[_] $ H.unit-r h)
          (λ _ → prop-has-all-paths-↓ (SetQuot-level _ _))

        assoc : ∀ h₁ h₂ h₃ → comp (comp h₁ h₂) h₃ == comp h₁ (comp h₂ h₃)
        assoc = SetQuot-elim
          (λ _ → Π-is-set λ _ → Π-is-set λ _ → =-preserves-set SetQuot-level)
          (λ h₁ → SetQuot-elim
            (λ _ → Π-is-set λ _ → =-preserves-set SetQuot-level)
            (λ h₂ → SetQuot-elim
              (λ _ → =-preserves-set SetQuot-level)
              (λ h₃ → ap q[_] $ H.assoc h₁ h₂ h₃)
              (λ _ → prop-has-all-paths-↓ (SetQuot-level _ _)))
            (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → SetQuot-level _ _)))
          (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → Π-is-prop λ _ → SetQuot-level _ _))

        inv-l : ∀ h → comp (inv h) h == ident
        inv-l = SetQuot-elim
          (λ _ → =-preserves-set SetQuot-level)
          (λ h → ap q[_] $ H.inv-l h)
          (λ _ → prop-has-all-paths-↓ (SetQuot-level _ _))

        inv-r : ∀ h → comp h (inv h) == ident
        inv-r = SetQuot-elim
          (λ _ → =-preserves-set SetQuot-level)
          (λ h → ap q[_] $ H.inv-r h)
          (λ _ → prop-has-all-paths-↓ (SetQuot-level _ _))

  Coker : Group (lmax i j)
  Coker = group _ SetQuot-level coker-struct

  module Coker = Group Coker

  {- correctness -}

  Coker-β : Coker ≃ᴳ QuotGroup (im-npropᴳ φ H-ab)
  Coker-β = ≃-to-≃ᴳ (ide _) to-pres-comp where
    abstract
      to-pres-comp : preserves-comp Coker.comp
        (QuotGroup.comp (im-npropᴳ φ H-ab)) (idf _)
      to-pres-comp = SetQuot-elim
        (λ _ → Π-is-set λ _ → =-preserves-set SetQuot-level)
        (λ _ → SetQuot-elim
          (λ _ → =-preserves-set SetQuot-level)
          (λ _ → idp)
          (λ _ → prop-has-all-paths-↓ (SetQuot-level _ _)))
        (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → SetQuot-level _ _))
