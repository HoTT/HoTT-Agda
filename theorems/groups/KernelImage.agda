{-# OPTIONS --without-K --rewriting #-}

open import HoTT

-- an attempt to speed up [QuotGroup (quot-of-sub (ker-prop ...) (im-nprop ...))]
-- which removes most intermediate constructions

module groups.KernelImage {i j k}
  {G : Group i} {H : Group j} {K : Group k}
  (ψ : H →ᴳ K) (φ : G →ᴳ H) (H-ab : is-abelian H) where

  --  G ---φ--→ᴳ H ---ψ--→ᴳ K

  private
    module G = Group G
    module H = AbGroup (H , H-ab)
    module K = Group K
    module ψ = GroupHom ψ
    module φ = GroupHom φ

    module Kerψ = Subgroup (ker-propᴳ ψ)

  ker/im-rel' : Rel H.El (lmax i j)
  ker/im-rel' h₁ h₂ = Trunc -1 (hfiber φ.f (H.diff h₁ h₂))

  ker/im-rel : Rel Kerψ.El (lmax i j)
  ker/im-rel ker₁ ker₂ = Trunc -1 (hfiber φ.f (H.diff (fst ker₁) (fst ker₂)))

  private
    ker/im-El : Type (lmax (lmax i j) k)
    ker/im-El = SetQuot ker/im-rel

  ker/im-struct : GroupStructure ker/im-El
  ker/im-struct = record {M} where
    module M where
      ident : ker/im-El
      ident = q[ H.ident , lemma ]
        where abstract lemma = ψ.pres-ident

      inv : ker/im-El → ker/im-El
      inv = SetQuot-rec inv' inv-rel
        where
          inv' : Kerψ.El → ker/im-El
          inv' (h , ψh=0) = q[ H.inv h , lemma ]
            where abstract lemma = ψ.pres-inv h ∙ ap K.inv ψh=0 ∙ K.inv-ident

          abstract
            inv-rel : ∀ {ker₁ ker₂} → ker/im-rel ker₁ ker₂ → inv' ker₁ == inv' ker₂
            inv-rel {h₁ , _} {h₂ , _} = Trunc-rec
              λ{(g , φg=h₁h₂⁻¹) → quot-rel
                [ G.inv g , φ.pres-inv g ∙ ap H.inv φg=h₁h₂⁻¹
                          ∙ H.inv-diff h₁ h₂ ∙ H.comm h₂ (H.inv h₁)
                          ∙ ap (H.comp (H.inv h₁)) (! (H.inv-inv h₂)) ]}

      comp : ker/im-El → ker/im-El → ker/im-El
      comp = SetQuot-rec comp' comp-rel where

        comp' : Kerψ.El → ker/im-El → ker/im-El
        comp' (h₁ , ψh₁=0) = SetQuot-rec comp'' comp'-rel where

          comp'' : Kerψ.El → ker/im-El
          comp'' (h₂ , ψh₂=0) = q[ H.comp h₁ h₂ , lemma ]
            where abstract lemma = ψ.pres-comp h₁ h₂ ∙ ap2 K.comp ψh₁=0 ψh₂=0
                                 ∙ K.unit-l K.ident

          abstract
            comp'-rel : ∀ {ker₂ ker₂'} → ker/im-rel ker₂ ker₂' → comp'' ker₂ == comp'' ker₂'
            comp'-rel {h₂ , _} {h₂' , _} = Trunc-rec
              λ{(g , φg=h₂h₂'⁻¹) → quot-rel
                [ g , ! ( ap (H.comp (H.comp h₁ h₂)) (H.inv-comp h₁ h₂')
                        ∙ H.assoc h₁ h₂ (H.comp (H.inv h₂') (H.inv h₁))
                        ∙ ap (H.comp h₁) (! $ H.assoc h₂ (H.inv h₂') (H.inv h₁))
                        ∙ H.comm h₁ (H.comp (H.comp h₂ (H.inv h₂')) (H.inv h₁))
                        ∙ H.assoc (H.comp h₂ (H.inv h₂')) (H.inv h₁) h₁
                        ∙ ap2 H.comp (! φg=h₂h₂'⁻¹) (H.inv-l h₁)
                        ∙ H.unit-r (φ.f g) )]}

        abstract
          comp-rel : ∀ {ker₁ ker₁'} → ker/im-rel ker₁ ker₁' → comp' ker₁ == comp' ker₁'
          comp-rel {h₁ , _} {h₁' , _} = Trunc-rec
            λ{(g , φg=h₁h₁'⁻¹) → λ= $ SetQuot-elim
              (λ{(h₂ , _) → quot-rel
                  [ g , ! ( ap (H.comp (H.comp h₁ h₂)) (H.inv-comp h₁' h₂)
                          ∙ H.assoc h₁ h₂ (H.comp (H.inv h₂) (H.inv h₁'))
                          ∙ ap (H.comp h₁) ( ! (H.assoc h₂ (H.inv h₂) (H.inv h₁'))
                                          ∙ ap (λ h → H.comp h (H.inv h₁')) (H.inv-r h₂)
                                          ∙ H.unit-l (H.inv h₁'))
                          ∙ ! φg=h₁h₁'⁻¹ )]})
              (λ _ → prop-has-all-paths-↓)}

      abstract
        unit-l : ∀ k/i → comp ident k/i == k/i
        unit-l = SetQuot-elim
          (λ{(h , _) → ap q[_] $ Kerψ.El=-out (H.unit-l h)})
          (λ _ → prop-has-all-paths-↓)

        assoc : ∀ k/i₁ k/i₂ k/i₃ → comp (comp k/i₁ k/i₂) k/i₃ == comp k/i₁ (comp k/i₂ k/i₃)
        assoc = SetQuot-elim
          (λ{(h₁ , _) → SetQuot-elim
            (λ{(h₂ , _) → SetQuot-elim
              (λ{(h₃ , _) → ap q[_] $ Kerψ.El=-out (H.assoc h₁ h₂ h₃)})
              (λ _ → prop-has-all-paths-↓)})
            (λ _ → prop-has-all-paths-↓)})
          (λ _ → prop-has-all-paths-↓)

        inv-l : ∀ k/i → comp (inv k/i) k/i == ident
        inv-l = SetQuot-elim
          (λ{(h , _) → ap q[_] $ Kerψ.El=-out (H.inv-l h)})
          (λ _ → prop-has-all-paths-↓)

  Ker/Im : Group (lmax i (lmax j k))
  Ker/Im = group _ ker/im-struct

  module Ker/Im = Group Ker/Im

  {- correctness -}

  Ker/Im-β : Ker/Im ≃ᴳ QuotGroup (quot-of-sub (ker-propᴳ ψ) (im-npropᴳ φ H-ab))
  Ker/Im-β = ≃-to-≃ᴳ (ide _) to-pres-comp where
    abstract
      to-pres-comp : preserves-comp Ker/Im.comp
        (QuotGroup.comp (quot-of-sub (ker-propᴳ ψ) (im-npropᴳ φ H-ab))) (idf _)
      to-pres-comp = SetQuot-elim
        (λ _ → SetQuot-elim
          (λ _ → ap q[_] $ Ker.El=-out ψ idp)
          (λ _ → prop-has-all-paths-↓))
        (λ _ → prop-has-all-paths-↓)
