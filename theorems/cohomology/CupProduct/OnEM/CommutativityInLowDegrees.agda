{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane
open import homotopy.EilenbergMacLane1
open import homotopy.EilenbergMacLaneFunctor

module cohomology.CupProduct.OnEM.CommutativityInLowDegrees where

module _ {i} {j} (G : AbGroup i) (H : AbGroup j) where

  private
    module G = AbGroup G
    module H = AbGroup H
    module G⊗H = TensorProduct G H
    module H⊗G = TensorProduct H G

  import cohomology.CupProduct.OnEM.InLowDegrees G H as GH
  import cohomology.CupProduct.OnEM.InLowDegrees H G as HG
  open EMExplicit

  ×-cp₀₀-comm : EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap 0 ∘ GH.×-cp₀₀
              ∼ HG.×-cp₀₀ ∘ ×-swap
  ×-cp₀₀-comm (g' , h') =
    (EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap 0 $
     emloop $
     (<– (emloop-equiv G.grp) g') G⊗H.⊗ (<– (emloop-equiv H.grp) h'))
      =⟨ EM₁-fmap-emloop-β G⊗H.swap $
         (<– (emloop-equiv G.grp) g') G⊗H.⊗ (<– (emloop-equiv H.grp) h') ⟩
    (emloop $
     GroupHom.f G⊗H.swap $
     (<– (emloop-equiv G.grp) g') G⊗H.⊗ (<– (emloop-equiv H.grp) h'))
      =⟨ ap emloop $ G⊗H.swap-β (<– (emloop-equiv G.grp) g') (<– (emloop-equiv H.grp) h') ⟩
    (emloop $
     (<– (emloop-equiv H.grp) h') H⊗G.⊗ (<– (emloop-equiv G.grp) g')) =∎

  ⊙×-cp₀₀-comm :
    ⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap 0 ◃⊙∘
    GH.⊙×-cp₀₀ ◃⊙idf
    =⊙∘
    HG.⊙×-cp₀₀ ◃⊙∘
    ⊙×-swap ◃⊙idf
  ⊙×-cp₀₀-comm =
    ⊙seq-λ= ×-cp₀₀-comm $
    contr-center $ =ₛ-level {n = -2} $ EM-level H⊗G.abgroup 0

module CP₀₁-comm {i} {j} (G : AbGroup i) (H : AbGroup j) where

  private
    module G = AbGroup G
    module H = AbGroup H
    module G⊗H = TensorProduct G H
    module H⊗G = TensorProduct H G

  import cohomology.CupProduct.OnEM.InLowDegrees G H as GH
  import cohomology.CupProduct.OnEM.InLowDegrees H G as HG

  private
    swap : H⊗G.grp →ᴳ G⊗H.grp
    swap = H⊗G.swap
    module swap = GroupHom swap

  cp₀₁-comm : ∀ g h →
    ap (GH.cp₀₁ g) (emloop h) ==
    ap (EM₁-fmap swap ∘ HG.cp₀₁ h) (emloop g)
  cp₀₁-comm g h =
    ap (GH.cp₀₁ g) (emloop h)
      =⟨ GH.cp₀₁-emloop-β g h ⟩
    emloop (g G⊗H.⊗ h)
      =⟨ ap emloop (! (H⊗G.swap-β h g)) ⟩
    emloop (swap.f (h H⊗G.⊗ g))
      =⟨ ! (EM₁-fmap-emloop-β swap (h H⊗G.⊗ g)) ⟩
    ap (EM₁-fmap swap) (emloop (h H⊗G.⊗ g))
      =⟨ ap (ap (EM₁-fmap swap)) (! (HG.cp₀₁-emloop-β h g)) ⟩
    ap (EM₁-fmap swap) (ap (HG.cp₀₁ h) (emloop g))
      =⟨ ∘-ap (EM₁-fmap swap) (HG.cp₀₁ h) (emloop g) ⟩
    ap (EM₁-fmap swap ∘ HG.cp₀₁ h) (emloop g) =∎

module CP₁₁-comm {i} {j} (G : AbGroup i) (H : AbGroup j) where

  private
    module G = AbGroup G
    module H = AbGroup H
    module G⊗H = TensorProduct G H
    module H⊗G = TensorProduct H G
    module swap = GroupHom H⊗G.swap

    import cohomology.CupProduct.OnEM.InLowDegrees G H as GH
    import cohomology.CupProduct.OnEM.InLowDegrees H G as HG

    infix 80 _G∪H_
    _G∪H_ : EM₁ G.grp → EM₁ H.grp → EMExplicit.EM G⊗H.abgroup 2
    _G∪H_ = GH.cp₁₁

    infix 80 _H∪G_
    _H∪G_ : EM₁ H.grp → EM₁ G.grp → EMExplicit.EM H⊗G.abgroup 2
    _H∪G_ = HG.cp₁₁

  ⊙−₁ : ⊙EM₁ H⊗G.grp ⊙→ ⊙EM₁ G⊗H.grp
  ⊙−₁ = ⊙EM₁-fmap (inv-hom G⊗H.abgroup) ⊙∘ ⊙EM₁-fmap H⊗G.swap

  −₁ : EM₁ H⊗G.grp → EM₁ G⊗H.grp
  −₁ = fst ⊙−₁

  − : EMExplicit.EM H⊗G.abgroup 2 → EMExplicit.EM G⊗H.abgroup 2
  − = Trunc-fmap (Susp-fmap −₁)

  ⊙− : EMExplicit.⊙EM H⊗G.abgroup 2 ⊙→ EMExplicit.⊙EM G⊗H.abgroup 2
  ⊙− = ⊙Trunc-fmap (⊙Susp-fmap −₁)

  comm-embase-emloop-seq : ∀ h →
    ap (λ y → embase G∪H y) (emloop h) =-=
    ap (λ y → − (y H∪G embase)) (emloop h)
  comm-embase-emloop-seq h =
    ap (λ y → embase G∪H y) (emloop h)
      =⟪idp⟫
    ap (cst [ north ]₂) (emloop h)
      =⟪ ap-cst [ north ]₂ (emloop h) ⟫
    idp
      =⟪idp⟫
    ap − (idp {a = [ north ]})
      =⟪ ! (ap (ap −) (HG.ap-cp₁₁-embase h)) ⟫
    ap − (ap (_H∪G embase) (emloop h))
      =⟪ ∘-ap − (_H∪G embase) (emloop h) ⟫
    ap (λ y → − (y H∪G embase)) (emloop h) ∎∎

  comm-emloop-embase-seq : ∀ g →
    ap (_G∪H embase) (emloop g) =-=
    ap (λ x → − (embase H∪G x)) (emloop g)
  comm-emloop-embase-seq g =
    ap (_G∪H embase) (emloop g)
      =⟪ GH.ap-cp₁₁-embase g ⟫
    idp
      =⟪ ! (ap-cst [ north ]₂ (emloop g)) ⟫
    ap (cst [ north ]₂) (emloop g)
      =⟪idp⟫
    ap (λ x → − (embase H∪G x)) (emloop g) ∎∎

  comm-embase-emloop' : ∀ h →
    ap (embase G∪H_) (emloop h) ==
    ap (λ y → − (y H∪G embase)) (emloop h)
  comm-embase-emloop' h = ↯ (comm-embase-emloop-seq h)

  comm-emloop-embase' : ∀ g →
    ap (λ x → GH.cp₁₁ x embase) (emloop g) ==
    ap (λ x → − (embase H∪G x)) (emloop g)
  comm-emloop-embase' g = ↯ (comm-emloop-embase-seq g)

  abstract

    comm-embase-emloop-comp' : ∀ h₁ h₂ →
      comm-embase-emloop' (H.comp h₁ h₂) ◃∙
      ap (ap (λ y → − (y H∪G embase))) (emloop-comp h₁ h₂) ◃∎
      =ₛ
      ap (ap (embase G∪H_)) (emloop-comp h₁ h₂) ◃∙
      ap-∙ (embase G∪H_) (emloop h₁) (emloop h₂) ◃∙
      ap2 _∙_ (comm-embase-emloop' h₁) (comm-embase-emloop' h₂) ◃∙
      ∙-ap (λ y → − (y H∪G embase)) (emloop h₁) (emloop h₂) ◃∎
    comm-embase-emloop-comp' h₁ h₂ =
      comm-embase-emloop' (H.comp h₁ h₂) ◃∙
      ap (ap (λ y → − (y H∪G embase))) (emloop-comp h₁ h₂) ◃∎
        =ₛ⟨ 0 & 1 & expand (comm-embase-emloop-seq (H.comp h₁ h₂)) ⟩
      ap-cst [ north ] (emloop (H.comp h₁ h₂)) ◃∙
      ! (ap (ap −) (HG.ap-cp₁₁-embase (H.comp h₁ h₂))) ◃∙
      ∘-ap − (_H∪G embase) (emloop (H.comp h₁ h₂)) ◃∙
      ap (ap (λ y → − (y H∪G embase))) (emloop-comp h₁ h₂) ◃∎
        =ₛ⟨ 2 & 2 & !ₛ $
            homotopy-naturality (ap − ∘ ap (_H∪G embase))
                                (ap (λ y → − (y H∪G embase)))
                                (∘-ap − (_H∪G embase))
                                (emloop-comp h₁ h₂) ⟩
      ap-cst [ north ] (emloop (H.comp h₁ h₂)) ◃∙
      ! (ap (ap −) (HG.ap-cp₁₁-embase (H.comp h₁ h₂))) ◃∙
      ap (ap − ∘ ap (_H∪G embase)) (emloop-comp h₁ h₂) ◃∙
      ∘-ap − (_H∪G embase) (emloop h₁ ∙ emloop h₂) ◃∎
        =ₛ₁⟨ 1 & 1 & !-ap (ap −) (HG.ap-cp₁₁-embase (H.comp h₁ h₂)) ⟩
      ap-cst [ north ] (emloop (H.comp h₁ h₂)) ◃∙
      ap (ap −) (! (HG.ap-cp₁₁-embase (H.comp h₁ h₂))) ◃∙
      ap (ap − ∘ ap (_H∪G embase)) (emloop-comp h₁ h₂) ◃∙
      ∘-ap − (_H∪G embase) (emloop h₁ ∙ emloop h₂) ◃∎
        =ₛ₁⟨ 2 & 1 & ap-∘ (ap −) (ap (_H∪G embase)) (emloop-comp h₁ h₂) ⟩
      ap-cst [ north ] (emloop (H.comp h₁ h₂)) ◃∙
      ap (ap −) (! (HG.ap-cp₁₁-embase (H.comp h₁ h₂))) ◃∙
      ap (ap −) (ap (ap (_H∪G embase)) (emloop-comp h₁ h₂)) ◃∙
      ∘-ap − (_H∪G embase) (emloop h₁ ∙ emloop h₂) ◃∎
        =ₛ⟨ 1 & 2 &
            ap-seq-=ₛ (ap −) $
            post-rotate-seq-in {p = _ ◃∙ _ ◃∎} $
            pre-rotate'-in $
            !ₛ $ HG.ap-cp₁₁-embase-coh h₁ h₂ ⟩
      ap-cst [ north ] (emloop (H.comp h₁ h₂)) ◃∙
      ap (ap −) (! (ap2 _∙_ (HG.ap-cp₁₁-embase h₁) (HG.ap-cp₁₁-embase h₂))) ◃∙
      ap (ap −) (! (ap-∙ (_H∪G embase) (emloop h₁) (emloop h₂))) ◃∙
      ∘-ap − (_H∪G embase) (emloop h₁ ∙ emloop h₂) ◃∎
        =ₛ₁⟨ 2 & 1 & ap-! (ap −) (ap-∙ (_H∪G embase) (emloop h₁) (emloop h₂))⟩
      ap-cst [ north ] (emloop (H.comp h₁ h₂)) ◃∙
      ap (ap −) (! (ap2 _∙_ (HG.ap-cp₁₁-embase h₁) (HG.ap-cp₁₁-embase h₂))) ◃∙
      ! (ap (ap −) (ap-∙ (_H∪G embase) (emloop h₁) (emloop h₂))) ◃∙
      ∘-ap − (_H∪G embase) (emloop h₁ ∙ emloop h₂) ◃∎
        =ₛ₁⟨ 3 & 1 & ! (!ap-∘=∘-ap − (_H∪G embase) (emloop h₁ ∙ emloop h₂)) ⟩
      ap-cst [ north ] (emloop (H.comp h₁ h₂)) ◃∙
      ap (ap −) (! (ap2 _∙_ (HG.ap-cp₁₁-embase h₁) (HG.ap-cp₁₁-embase h₂))) ◃∙
      ! (ap (ap −) (ap-∙ (_H∪G embase) (emloop h₁) (emloop h₂))) ◃∙
      ! (ap-∘ − (_H∪G embase) (emloop h₁ ∙ emloop h₂)) ◃∎
        =ₛ⟨ 2 & 2 &
            post-rotate-seq-in {p = _ ◃∙ _ ◃∎} $
            pre-rotate'-seq-in {p = _ ◃∙ _ ◃∎} $
            ap-∘-∙-coh − (_H∪G embase) (emloop h₁) (emloop h₂) ⟩
      ap-cst [ north ] (emloop (H.comp h₁ h₂)) ◃∙
      ap (ap −) (! (ap2 _∙_ (HG.ap-cp₁₁-embase h₁) (HG.ap-cp₁₁-embase h₂))) ◃∙
      ap-∙ − (ap (_H∪G embase) (emloop h₁)) (ap (_H∪G embase) (emloop h₂)) ◃∙
      ! (ap2 _∙_ (ap-∘ − (_H∪G embase) (emloop h₁))
                 (ap-∘ − (_H∪G embase) (emloop h₂))) ◃∙
      ! (ap-∙ (λ y → − (y H∪G embase)) (emloop h₁) (emloop h₂)) ◃∎
        =ₛ₁⟨ 1 & 1 &
              ap (ap (ap −)) (!-ap2 _∙_ (HG.ap-cp₁₁-embase h₁) (HG.ap-cp₁₁-embase h₂)) ∙
              ap-ap2 (ap −) _∙_ (! (HG.ap-cp₁₁-embase h₁)) (! (HG.ap-cp₁₁-embase h₂)) ⟩
      ap-cst [ north ] (emloop (H.comp h₁ h₂)) ◃∙
      ap2 (λ p q → ap − (p ∙ q)) (! (HG.ap-cp₁₁-embase h₁)) (! (HG.ap-cp₁₁-embase h₂)) ◃∙
      ap-∙ − (ap (_H∪G embase) (emloop h₁)) (ap (_H∪G embase) (emloop h₂)) ◃∙
      ! (ap2 _∙_ (ap-∘ − (_H∪G embase) (emloop h₁))
                 (ap-∘ − (_H∪G embase) (emloop h₂))) ◃∙
      ! (ap-∙ (λ y → − (y H∪G embase)) (emloop h₁) (emloop h₂)) ◃∎
        =ₛ⟨ 1 & 2 &
            homotopy-naturality2 (λ p q → ap − (p ∙ q))
                                  (λ p q → ap − p ∙ ap − q)
                                  (λ p q → ap-∙ − p q)
                                  (! (HG.ap-cp₁₁-embase h₁))
                                  (! (HG.ap-cp₁₁-embase h₂)) ⟩
      ap-cst [ north ] (emloop (H.comp h₁ h₂)) ◃∙
      idp ◃∙
      ap2 (λ p q → ap − p ∙ ap − q) (! (HG.ap-cp₁₁-embase h₁)) (! (HG.ap-cp₁₁-embase h₂)) ◃∙
      ! (ap2 _∙_ (ap-∘ − (_H∪G embase) (emloop h₁))
                 (ap-∘ − (_H∪G embase) (emloop h₂))) ◃∙
      ! (ap-∙ (λ y → − (y H∪G embase)) (emloop h₁) (emloop h₂)) ◃∎
        =ₛ⟨ 1 & 1 & expand [] ⟩
      ap-cst [ north ] (emloop (H.comp h₁ h₂)) ◃∙
      ap2 (λ p q → ap − p ∙ ap − q) (! (HG.ap-cp₁₁-embase h₁)) (! (HG.ap-cp₁₁-embase h₂)) ◃∙
      ! (ap2 _∙_ (ap-∘ − (_H∪G embase) (emloop h₁))
                 (ap-∘ − (_H∪G embase) (emloop h₂))) ◃∙
      ! (ap-∙ (λ y → − (y H∪G embase)) (emloop h₁) (emloop h₂)) ◃∎
        =ₛ₁⟨ 1 & 1 &
              ! (ap2-ap-lr _∙_ (ap −) (ap −) (! (HG.ap-cp₁₁-embase h₁)) (! (HG.ap-cp₁₁-embase h₂))) ∙
              ap2 (ap2 _∙_) (ap-! (ap −) (HG.ap-cp₁₁-embase h₁)) (ap-! (ap −) (HG.ap-cp₁₁-embase h₂)) ⟩
      ap-cst [ north ] (emloop (H.comp h₁ h₂)) ◃∙
      ap2 _∙_ (! (ap (ap −) (HG.ap-cp₁₁-embase h₁))) (! (ap (ap −) (HG.ap-cp₁₁-embase h₂))) ◃∙
      ! (ap2 _∙_ (ap-∘ − (_H∪G embase) (emloop h₁))
                 (ap-∘ − (_H∪G embase) (emloop h₂))) ◃∙
      ! (ap-∙ (λ y → − (y H∪G embase)) (emloop h₁) (emloop h₂)) ◃∎
        =ₛ₁⟨ 2 & 1 &
            !-ap2 _∙_ (ap-∘ − (_H∪G embase) (emloop h₁))
                      (ap-∘ − (_H∪G embase) (emloop h₂)) ∙
            ap2 (ap2 _∙_) (!ap-∘=∘-ap − (_H∪G embase) (emloop h₁))
                          (!ap-∘=∘-ap − (_H∪G embase) (emloop h₂)) ⟩
      ap-cst [ north ] (emloop (H.comp h₁ h₂)) ◃∙
      ap2 _∙_ (! (ap (ap −) (HG.ap-cp₁₁-embase h₁))) (! (ap (ap −) (HG.ap-cp₁₁-embase h₂))) ◃∙
      ap2 _∙_ (∘-ap − (_H∪G embase) (emloop h₁))
              (∘-ap − (_H∪G embase) (emloop h₂)) ◃∙
      ! (ap-∙ (λ y → − (y H∪G embase)) (emloop h₁) (emloop h₂)) ◃∎
        =ₛ₁⟨ 3 & 1 & !ap-∙=∙-ap (λ y → − (y H∪G embase)) (emloop h₁) (emloop h₂) ⟩
      ap-cst [ north ] (emloop (H.comp h₁ h₂)) ◃∙
      ap2 _∙_ (! (ap (ap −) (HG.ap-cp₁₁-embase h₁))) (! (ap (ap −) (HG.ap-cp₁₁-embase h₂))) ◃∙
      ap2 _∙_ (∘-ap − (_H∪G embase) (emloop h₁))
              (∘-ap − (_H∪G embase) (emloop h₂)) ◃∙
      ∙-ap (λ y → − (y H∪G embase)) (emloop h₁) (emloop h₂) ◃∎
        =ₛ⟨ 0 & 1 &
            ap-cst [ north ] (emloop (H.comp h₁ h₂)) ◃∎
              =ₛ⟨ 1 & 0 & contract ⟩
            ap-cst [ north ] (emloop (H.comp h₁ h₂)) ◃∙
            idp ◃∎
              =ₛ₁⟨ 1 & 1 & ! (ap-cst idp (emloop-comp h₁ h₂)) ⟩
            ap-cst [ north ] (emloop (H.comp h₁ h₂)) ◃∙
            ap (λ _ → idp) (emloop-comp h₁ h₂) ◃∎
              =ₛ⟨ !ₛ $ homotopy-naturality (ap (embase G∪H_))
                                           (λ _ → idp)
                                           (ap-cst [ north ])
                                           (emloop-comp h₁ h₂) ⟩
            ap (ap (embase G∪H_)) (emloop-comp h₁ h₂) ◃∙
            ap-cst [ north ] (emloop h₁ ∙ emloop h₂) ◃∎
              =ₛ⟨ 1 & 1 & ap-cst-coh [ north ] (emloop h₁) (emloop h₂) ⟩
            ap (ap (embase G∪H_)) (emloop-comp h₁ h₂) ◃∙
            ap-∙ (cst [ north ]) (emloop h₁) (emloop h₂) ◃∙
            ap2 _∙_ (ap-cst [ north ] (emloop h₁)) (ap-cst [ north ] (emloop h₂)) ◃∎ ∎ₛ
          ⟩
      ap (ap (embase G∪H_)) (emloop-comp h₁ h₂) ◃∙
      ap-∙ (cst [ north ]) (emloop h₁) (emloop h₂) ◃∙
      ap2 _∙_ (ap-cst [ north ] (emloop h₁)) (ap-cst [ north ] (emloop h₂)) ◃∙
      ap2 _∙_ (! (ap (ap −) (HG.ap-cp₁₁-embase h₁))) (! (ap (ap −) (HG.ap-cp₁₁-embase h₂))) ◃∙
      ap2 _∙_ (∘-ap − (_H∪G embase) (emloop h₁))
              (∘-ap − (_H∪G embase) (emloop h₂)) ◃∙
      ∙-ap (λ y → − (y H∪G embase)) (emloop h₁) (emloop h₂) ◃∎
        =ₛ⟨ 2 & 3 & ∙-ap2-seq _∙_ (comm-embase-emloop-seq h₁) (comm-embase-emloop-seq h₂) ⟩
      ap (ap (embase G∪H_)) (emloop-comp h₁ h₂) ◃∙
      ap-∙ (embase G∪H_) (emloop h₁) (emloop h₂) ◃∙
      ap2 _∙_ (comm-embase-emloop' h₁) (comm-embase-emloop' h₂) ◃∙
      ∙-ap (λ y → − (y H∪G embase)) (emloop h₁) (emloop h₂) ◃∎ ∎ₛ

    comm-emloop-comp-embase' : ∀ g₁ g₂ →
      comm-emloop-embase' (G.comp g₁ g₂) ◃∙
      ap (ap (λ x → − (embase H∪G x))) (emloop-comp g₁ g₂) ◃∎
      =ₛ
      ap (ap (_G∪H embase)) (emloop-comp g₁ g₂) ◃∙
      ap-∙ (_G∪H embase) (emloop g₁) (emloop g₂) ◃∙
      ap2 _∙_ (comm-emloop-embase' g₁) (comm-emloop-embase' g₂) ◃∙
      ∙-ap (λ x → − (embase H∪G x)) (emloop g₁) (emloop g₂) ◃∎
    comm-emloop-comp-embase' g₁ g₂ =
      comm-emloop-embase' (G.comp g₁ g₂) ◃∙
      ap (ap (λ x → − (embase H∪G x))) (emloop-comp g₁ g₂) ◃∎
        =ₛ⟨ 0 & 1 & expand (comm-emloop-embase-seq (G.comp g₁ g₂)) ⟩
      GH.ap-cp₁₁-embase (G.comp g₁ g₂) ◃∙
      ! (ap-cst [ north ] (emloop (G.comp g₁ g₂))) ◃∙
      ap (ap (λ x → − (embase H∪G x))) (emloop-comp g₁ g₂) ◃∎
        =ₛ⟨ 1 & 2 & !ₛ $
            homotopy-naturality
              (λ _ → idp)
              (ap (cst [ north ]))
              (λ p → ! (ap-cst [ north ] p))
              (emloop-comp g₁ g₂) ⟩
      GH.ap-cp₁₁-embase (G.comp g₁ g₂) ◃∙
      ap (λ _ → idp) (emloop-comp g₁ g₂) ◃∙
      ! (ap-cst [ north ] (emloop g₁ ∙ emloop g₂)) ◃∎
        =ₛ⟨ 1 & 1 & =ₛ-in {t = []} (ap-cst idp (emloop-comp g₁ g₂)) ⟩
      GH.ap-cp₁₁-embase (G.comp g₁ g₂) ◃∙
      ! (ap-cst [ north ] (emloop g₁ ∙ emloop g₂)) ◃∎
        =ₛ⟨ 0 & 1 & GH.ap-cp₁₁-embase-coh g₁ g₂ ⟩
      ap (ap (_G∪H embase)) (emloop-comp g₁ g₂) ◃∙
      ap-∙ (_G∪H embase) (emloop g₁) (emloop g₂) ◃∙
      ap2 _∙_ (GH.ap-cp₁₁-embase g₁) (GH.ap-cp₁₁-embase g₂) ◃∙
      ! (ap-cst [ north ] (emloop g₁ ∙ emloop g₂)) ◃∎
        =ₛ⟨ 3 & 1 & !-=ₛ $ ap-cst-coh [ north ] (emloop g₁) (emloop g₂) ⟩
      ap (ap (_G∪H embase)) (emloop-comp g₁ g₂) ◃∙
      ap-∙ (_G∪H embase) (emloop g₁) (emloop g₂) ◃∙
      ap2 _∙_ (GH.ap-cp₁₁-embase g₁) (GH.ap-cp₁₁-embase g₂) ◃∙
      ! (ap2 _∙_ (ap-cst [ north ] (emloop g₁)) (ap-cst [ north ] (emloop g₂))) ◃∙
      ! (ap-∙ (cst [ north ]) (emloop g₁) (emloop g₂)) ◃∎
        =ₛ₁⟨ 3 & 1 & ! (ap2-! _∙_ (ap-cst [ north ] (emloop g₁)) (ap-cst [ north ] (emloop g₂))) ⟩
      ap (ap (_G∪H embase)) (emloop-comp g₁ g₂) ◃∙
      ap-∙ (_G∪H embase) (emloop g₁) (emloop g₂) ◃∙
      ap2 _∙_ (GH.ap-cp₁₁-embase g₁) (GH.ap-cp₁₁-embase g₂) ◃∙
      ap2 _∙_ (! (ap-cst [ north ] (emloop g₁))) (! (ap-cst [ north ] (emloop g₂))) ◃∙
      ! (ap-∙ (cst [ north ]) (emloop g₁) (emloop g₂)) ◃∎
        =ₛ⟨ 2 & 2 & ∙-ap2-seq _∙_ (comm-emloop-embase-seq g₁) (comm-emloop-embase-seq g₂) ⟩
      ap (ap (_G∪H embase)) (emloop-comp g₁ g₂) ◃∙
      ap-∙ (_G∪H embase) (emloop g₁) (emloop g₂) ◃∙
      ap2 _∙_ (comm-emloop-embase' g₁) (comm-emloop-embase' g₂) ◃∙
      ! (ap-∙ (cst [ north ]) (emloop g₁) (emloop g₂)) ◃∎
        =ₛ₁⟨ 3 & 1 & !ap-∙=∙-ap (cst [ north ]) (emloop g₁) (emloop g₂) ⟩
      ap (ap (_G∪H embase)) (emloop-comp g₁ g₂) ◃∙
      ap-∙ (_G∪H embase) (emloop g₁) (emloop g₂) ◃∙
      ap2 _∙_ (comm-emloop-embase' g₁) (comm-emloop-embase' g₂) ◃∙
      ∙-ap (cst [ north ]) (emloop g₁) (emloop g₂) ◃∎ ∎ₛ

    comm-emloop-emloop' : ∀ g h →
      ap-comm _G∪H_ (emloop g) (emloop h) ◃∙
      ap2 _∙_ (comm-embase-emloop' h) (comm-emloop-embase' g) ◃∎
      =ₛ
      ap2 _∙_ (comm-emloop-embase' g) (comm-embase-emloop' h) ◃∙
      ap-comm (λ x y → − (y H∪G x)) (emloop g) (emloop h) ◃∎
    comm-emloop-emloop' g h =
      ap-comm _G∪H_ (emloop g) (emloop h) ◃∙
      ap2 _∙_ (comm-embase-emloop' h) (comm-emloop-embase' g) ◃∎
        =ₛ⟨ 1 & 1 & ap2-out _∙_ (comm-embase-emloop' h) (comm-emloop-embase' g) ⟩
      ap-comm _G∪H_ (emloop g) (emloop h) ◃∙
      ap (_∙ ap (_G∪H embase) (emloop g)) (comm-embase-emloop' h) ◃∙
      ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_) (comm-emloop-embase' g) ◃∎
        =ₛ⟨ 1 & 1 & ap-seq-=ₛ (_∙ ap (_G∪H embase) (emloop g))
                              (take-drop-split 1 (comm-embase-emloop-seq h)) ⟩
      ap-comm _G∪H_ (emloop g) (emloop h) ◃∙
      ap (_∙ ap (_G∪H embase) (emloop g)) (ap-cst [ north ] (emloop h)) ◃∙
      ap (_∙ ap (_G∪H embase) (emloop g)) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
      ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_) (comm-emloop-embase' g) ◃∎
        =ₛ⟨ 3 & 1 & ap-seq-∙ (ap (λ y → − (y H∪G embase)) (emloop h) ∙_) (comm-emloop-embase-seq g) ⟩
      ap-comm _G∪H_ (emloop g) (emloop h) ◃∙
      ap (_∙ ap (_G∪H embase) (emloop g)) (ap-cst [ north ] (emloop h)) ◃∙
      ap (_∙ ap (_G∪H embase) (emloop g)) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
      ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_) (GH.ap-cp₁₁-embase g) ◃∙
      ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_) (! (ap-cst [ north ] (emloop g))) ◃∎
        =ₛ⟨ 4 & 1 & ap-seq-=ₛ (ap (λ y → − (y H∪G embase)) (emloop h) ∙_) step₄' ⟩
      ap-comm _G∪H_ (emloop g) (emloop h) ◃∙
      ap (_∙ ap (_G∪H embase) (emloop g)) (ap-cst [ north ] (emloop h)) ◃∙
      ap (_∙ ap (_G∪H embase) (emloop g)) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
      ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_) (GH.ap-cp₁₁-embase g) ◃∙
      ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_) (↯ h₁'-seq) ◃∙
      ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_) (! (!-inv-r (h₁' embase))) ◃∙
      ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_)
          (! (homotopy-to-cst-ap (λ x → [ north ]₂) h₁' (emloop g))) ◃∎
        =ₛ⟨ 2 & 2 & ap-comm-=ₛ _∙_ (↯ (tail (comm-embase-emloop-seq h))) (GH.ap-cp₁₁-embase g) ⟩
      ap-comm _G∪H_ (emloop g) (emloop h) ◃∙
      ap (_∙ ap (_G∪H embase) (emloop g)) (ap-cst [ north ] (emloop h)) ◃∙
      ap (idp ∙_) (GH.ap-cp₁₁-embase g) ◃∙
      ap (_∙ idp) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
      ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_) (↯ h₁'-seq) ◃∙
      ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_) (! (!-inv-r (h₁' embase))) ◃∙
      ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_)
          (! (homotopy-to-cst-ap (λ x → [ north ]₂) h₁' (emloop g))) ◃∎
        =ₛ⟨ 3 & 2 & ap-comm-=ₛ _∙_ (↯ (tail (comm-embase-emloop-seq h))) (↯ h₁'-seq) ⟩
      ap-comm _G∪H_ (emloop g) (emloop h) ◃∙
      ap (_∙ ap (_G∪H embase) (emloop g)) (ap-cst [ north ] (emloop h)) ◃∙
      ap (idp ∙_) (GH.ap-cp₁₁-embase g) ◃∙
      ap (idp ∙_) (↯ h₁'-seq) ◃∙
      ap (λ a → a ∙ idp) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
      ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_) (! (!-inv-r (h₁' embase))) ◃∙
      ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_)
          (! (homotopy-to-cst-ap (λ x → [ north ]₂) h₁' (emloop g))) ◃∎
        =ₛ₁⟨ 3 & 1 & ap (ap (idp ∙_)) (! (=ₛ-out heart))⟩
      ap-comm _G∪H_ (emloop g) (emloop h) ◃∙
      ap (_∙ ap (_G∪H embase) (emloop g)) (ap-cst [ north ] (emloop h)) ◃∙
      ap (idp ∙_) (GH.ap-cp₁₁-embase g) ◃∙
      ap (idp ∙_) (↯ h₁-seq) ◃∙
      ap (λ a → a ∙ idp) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
      ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_) (! (!-inv-r (h₁' embase))) ◃∙
      ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_)
          (! (homotopy-to-cst-ap (λ x → [ north ]₂) h₁' (emloop g))) ◃∎
        =ₛ⟨ 0 & 3 & top-part ⟩
      ap (ap (_G∪H embase) (emloop g) ∙_)
         (homotopy-to-cst-ap (λ y → [ north ]₂) h₁ (emloop h)) ◃∙
      ap (ap (_G∪H embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
      ap (_∙ idp) (GH.ap-cp₁₁-embase g) ◃∙
      ap (idp ∙_) (↯ h₁-seq) ◃∙
      ap (λ a → a ∙ idp) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
      ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_) (! (!-inv-r (h₁' embase))) ◃∙
      ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_)
         (! (homotopy-to-cst-ap (λ x → [ north ]₂) h₁' (emloop g))) ◃∎
        =ₛ⟨ 4 & 3 & bottom-part ⟩
      ap (ap (_G∪H embase) (emloop g) ∙_)
         (homotopy-to-cst-ap (λ y → [ north ]₂) h₁ (emloop h)) ◃∙
      ap (ap (_G∪H embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
      ap (_∙ idp) (GH.ap-cp₁₁-embase g) ◃∙
      ap (idp ∙_) (↯ h₁-seq) ◃∙
      ap (idp ∙_) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
      ap (_∙ ap (λ y → − (y H∪G embase)) (emloop h)) (! (ap-cst [ north ]₂ (emloop g))) ◃∙
      ap-comm (λ x y → − (y H∪G x)) (emloop g) (emloop h) ◃∎
        =ₛ⟨ 2 & 2 & ap-comm-=ₛ _∙_ (GH.ap-cp₁₁-embase g) (↯ h₁-seq) ⟩
      ap (ap (_G∪H embase) (emloop g) ∙_)
         (homotopy-to-cst-ap (λ y → [ north ]₂) h₁ (emloop h)) ◃∙
      ap (ap (_G∪H embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
      ap (ap (_G∪H embase) (emloop g) ∙_) (↯ h₁-seq) ◃∙
      ap (_∙ idp) (GH.ap-cp₁₁-embase g) ◃∙
      ap (idp ∙_) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
      ap (_∙ ap (λ y → − (y H∪G embase)) (emloop h)) (! (ap-cst [ north ]₂ (emloop g))) ◃∙
      ap-comm (λ x y → − (y H∪G x)) (emloop g) (emloop h) ◃∎
        =ₛ⟨ 3 & 2 & ap-comm-=ₛ _∙_ (GH.ap-cp₁₁-embase g) (↯ (tail (comm-embase-emloop-seq h))) ⟩
      ap (ap (_G∪H embase) (emloop g) ∙_)
         (homotopy-to-cst-ap (λ y → [ north ]₂) h₁ (emloop h)) ◃∙
      ap (ap (_G∪H embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
      ap (ap (_G∪H embase) (emloop g) ∙_) (↯ h₁-seq) ◃∙
      ap (ap (_G∪H embase) (emloop g) ∙_) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
      ap (_∙ ap (λ y → − (y H∪G embase)) (emloop h)) (GH.ap-cp₁₁-embase g) ◃∙
      ap (_∙ ap (λ y → − (y H∪G embase)) (emloop h)) (! (ap-cst [ north ]₂ (emloop g))) ◃∙
      ap-comm (λ x y → − (y H∪G x)) (emloop g) (emloop h) ◃∎
        =ₛ⟨ 4 & 2 & ∙-ap-seq (_∙ ap (λ y → − (y H∪G embase)) (emloop h)) (comm-emloop-embase-seq g) ⟩
      ap (ap (_G∪H embase) (emloop g) ∙_)
         (homotopy-to-cst-ap (λ y → [ north ]₂) h₁ (emloop h)) ◃∙
      ap (ap (_G∪H embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
      ap (ap (_G∪H embase) (emloop g) ∙_) (↯ h₁-seq) ◃∙
      ap (ap (_G∪H embase) (emloop g) ∙_) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
      ap (_∙ ap (λ y → − (y H∪G embase)) (emloop h)) (comm-emloop-embase' g) ◃∙
      ap-comm (λ x y → − (y H∪G x)) (emloop g) (emloop h) ◃∎
        =ₛ⟨ 0 & 3 & ap-seq-=ₛ (ap (_G∪H embase) (emloop g) ∙_) step₁₃' ⟩
      ap (ap (_G∪H embase) (emloop g) ∙_) (ap-cst [ north ]₂ (emloop h)) ◃∙
      ap (ap (_G∪H embase) (emloop g) ∙_) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
      ap (_∙ ap (λ y → − (y H∪G embase)) (emloop h)) (comm-emloop-embase' g) ◃∙
      ap-comm (λ x y → − (y H∪G x)) (emloop g) (emloop h) ◃∎
        =ₛ⟨ 0 & 2 & !ₛ $ ap-seq-=ₛ (ap (_G∪H embase) (emloop g) ∙_) $
                    take-drop-split 1 (comm-embase-emloop-seq h) ⟩
      ap (ap (_G∪H embase) (emloop g) ∙_) (comm-embase-emloop' h) ◃∙
      ap (_∙ ap (λ y → − (y H∪G embase)) (emloop h)) (comm-emloop-embase' g) ◃∙
      ap-comm (λ x y → − (y H∪G x)) (emloop g) (emloop h) ◃∎
        =ₛ⟨ 0 & 2 & !ₛ (ap2-out' _∙_ (comm-emloop-embase' g) (comm-embase-emloop' h)) ⟩
      ap2 _∙_ (comm-emloop-embase' g) (comm-embase-emloop' h) ◃∙
      ap-comm (λ x y → − (y H∪G x)) (emloop g) (emloop h) ◃∎ ∎ₛ
      where
      h₀ : ∀ y → embase G∪H y == [ north ]₂
      h₀ y = idp
      h₁ : ∀ y → embase G∪H y == [ north ]₂
      h₁ = transport (λ x → ∀ y → x G∪H y == [ north ]₂) (emloop g) h₀
      h₀' : ∀ x → − (embase H∪G x) == [ north ]₂
      h₀' x = idp
      h₁' : ∀ x → − (embase H∪G x) == [ north ]₂
      h₁' = transport (λ y → ∀ x → − (y H∪G x) == [ north ]₂) (emloop h) h₀'
      h₁-path : ∀ y → h₁ y == ! (ap [_]₂ (GH.η (GH.cp₀₁ g y)))
      h₁-path y =
        transport (λ x → ∀ y → x G∪H y == [ north ]₂) (emloop g) h₀ y
          =⟨ app= (transp-naturality {B = λ x → ∀ y → x G∪H y == [ north ]₂}
                                     {C = λ x → x G∪H y == [ north ]₂}
                                     (λ k → k y)
                                     (emloop g)) h₀ ⟩
        transport (λ x → x G∪H y == [ north ]₂) (emloop g) (h₀ y)
          =⟨ to-transp {B = λ x → x G∪H y == [ north ]₂} {p = emloop g} $
             ↓-app=cst-in {f = _G∪H y}
                          {p = emloop g} {u = idp}
                          {v = ! (ap (_G∪H y) (emloop g))} $
             ! (!-inv-r (ap (_G∪H y) (emloop g))) ⟩
        ! (ap (_G∪H y) (emloop g))
          =⟨ ap ! (GH.ap-cp₁₁ g y) ⟩
        ! (ap [_] (GH.η (GH.cp₀₁ g y))) =∎
      h₁'-path : ∀ x → h₁' x == ! (ap [_]₂ (GH.η (−₁ (HG.cp₀₁ h x))))
      h₁'-path x =
        transport (λ y → ∀ x → − (y H∪G x) == [ north ]₂) (emloop h) h₀' x
          =⟨ app= (transp-naturality {B = λ y → ∀ x → − (y H∪G x) == [ north ]₂}
                                     {C = λ y → − (y H∪G x) == [ north ]₂}
                                     (λ k → k x)
                                     (emloop h)) h₀' ⟩
        transport (λ y → − (y H∪G x) == [ north ]₂) (emloop h) (h₀' x)
          =⟨ to-transp {B = λ y → − (y H∪G x) == [ north ]₂} {p = emloop h} $
             ↓-app=cst-in {f = λ y → − (y H∪G x)}
                          {p = emloop h} {u = idp}
                          {v = ! (ap (λ y → − (y H∪G x)) (emloop h))} $
             ! (!-inv-r (ap (λ y → − (y H∪G x)) (emloop h))) ⟩
        ! (ap (λ y → − (y H∪G x)) (emloop h))
          =⟨ ap ! (ap-∘ − (_H∪G x) (emloop h)) ⟩
        ! (ap − (ap (_H∪G x) (emloop h)))
          =⟨ ap (! ∘ ap −) (HG.ap-cp₁₁ h x) ⟩
        ! (ap − (ap [_]₂ (HG.η (HG.cp₀₁ h x))))
          =⟨ ap ! (∘-ap − [_]₂ (HG.η (HG.cp₀₁ h x))) ⟩
        ! (ap (λ p → [ Susp-fmap −₁ p ]₂) (HG.η (HG.cp₀₁ h x)))
          =⟨ ap ! (ap-∘ [_]₂ (Susp-fmap −₁) (HG.η (HG.cp₀₁ h x))) ⟩
        ! (ap [_]₂ (ap (Susp-fmap −₁) (HG.η (HG.cp₀₁ h x))))
          =⟨ ! (ap (! ∘ ap [_]₂) (app= (ap fst (η-natural ⊙−₁)) (HG.cp₀₁ h x))) ⟩
        ! (ap [_]₂ (GH.η (−₁ (HG.cp₀₁ h x)))) =∎
        where open import homotopy.SuspAdjointLoop using (η-natural)
      h₁-seq : idp {a = [ north ]₂} =-= idp
      h₁-seq = ! (!-inv-r (h₁ embase)) ◃∙
                ap (λ v → h₁ v ∙ ! (h₁ embase)) (emloop h) ◃∙
                !-inv-r (h₁ embase) ◃∎
      h₁'-seq : idp {a = [ north ]₂} =-= idp
      h₁'-seq = ! (!-inv-r (h₁' embase)) ◃∙
                ! (ap (λ v → h₁' v ∙ ! (h₁' embase)) (emloop g)) ◃∙
                !-inv-r (h₁' embase) ◃∎
      {- the crucial step in the commutative diagram -}
      heart : h₁-seq =ₛ h₁'-seq
      heart =
        ! (!-inv-r (h₁ embase)) ◃∙
        ap (λ v → h₁ v ∙ ! (h₁ embase)) (emloop h) ◃∙
        !-inv-r (h₁ embase) ◃∎
          =ₛ⟨ =ₛ-in {t = ! (!-inv-r (! (ap [_]₂ (GH.η embase)))) ◃∙
                         ap (λ v → ! (ap [_]₂ (GH.η (GH.cp₀₁ g v))) ∙ ! (! (ap [_] (GH.η embase)))) (emloop h) ◃∙
                         !-inv-r (! (ap [_]₂ (GH.η embase))) ◃∎} $
              ap (λ f → ! (!-inv-r (f embase)) ∙
                        ap (λ v → f v ∙ ! (f embase)) (emloop h) ∙
                        !-inv-r (f embase))
                  (λ= h₁-path) ⟩
        ! (!-inv-r (! (ap [_]₂ (GH.η embase)))) ◃∙
        ap (λ v → ! (ap [_]₂ (GH.η (GH.cp₀₁ g v))) ∙ ! (! (ap [_]₂ (GH.η embase)))) (emloop h) ◃∙
        !-inv-r (! (ap [_]₂ (GH.η embase))) ◃∎
          =ₛ₁⟨ 1 & 1 &
                ap (λ v → ! (ap [_]₂ (GH.η (GH.cp₀₁ g v))) ∙ ! (! (ap [_]₂ (GH.η embase)))) (emloop h)
                  =⟨ ap-∘ (λ w → ! (ap [_]₂ (GH.η w)) ∙ ! (! (ap [_]₂ (GH.η embase)))) (GH.cp₀₁ g) (emloop h) ⟩
                ap (λ w → ! (ap [_]₂ (GH.η w)) ∙ ! (! (ap [_]₂ (GH.η embase)))) (ap (GH.cp₀₁ g) (emloop h))
                  =⟨ ap (ap (λ w → ! (ap [_]₂ (GH.η w)) ∙ ! (! (ap [_]₂ (GH.η embase))))) $
                    ap (GH.cp₀₁ g) (emloop h)
                      =⟨ CP₀₁-comm.cp₀₁-comm G H g h ⟩
                    ap (EM₁-fmap H⊗G.swap ∘ HG.cp₀₁ h) (emloop g)
                      =⟨ ! (!-! _) ⟩
                    ! (! (ap (EM₁-fmap H⊗G.swap ∘ HG.cp₀₁ h) (emloop g)))
                      =⟨ ap ! (! (EM₁-neg-! G⊗H.abgroup _)) ⟩
                    ! (ap (EM₁-neg G⊗H.abgroup) (ap (EM₁-fmap H⊗G.swap ∘ HG.cp₀₁ h) (emloop g)))
                      =⟨ ap ! (∘-ap (EM₁-neg G⊗H.abgroup) (EM₁-fmap H⊗G.swap ∘ HG.cp₀₁ h) (emloop g)) ⟩
                    ! (ap (−₁ ∘ HG.cp₀₁ h) (emloop g)) =∎
                    -- Yo dawg, I herd you like continued equalities,
                    -- so we put continued equalities into your continued equalities,
                    -- so u can reason equationally while u reason equationally.
                  ⟩
                ap (λ w → ! (ap [_]₂ (GH.η w)) ∙ ! (! (ap [_]₂ (GH.η embase)))) (! (ap (−₁ ∘ HG.cp₀₁ h) (emloop g)))
                  =⟨ ap-! (λ w → ! (ap [_]₂ (GH.η w)) ∙ ! (! (ap [_]₂ (GH.η embase)))) (ap (−₁ ∘ HG.cp₀₁ h) (emloop g)) ⟩
                ! (ap (λ w → ! (ap [_]₂ (GH.η w)) ∙ ! (! (ap [_]₂ (GH.η embase)))) (ap (−₁ ∘ HG.cp₀₁ h) (emloop g)))
                  =⟨ ap ! (∘-ap (λ w → ! (ap [_]₂ (GH.η w)) ∙ ! (! (ap [_]₂ (GH.η embase)))) (−₁ ∘ HG.cp₀₁ h) (emloop g)) ⟩
                ! (ap (λ v → ! (ap [_]₂ (GH.η (−₁ (HG.cp₀₁ h v)))) ∙ ! (! (ap [_]₂ (GH.η embase)))) (emloop g)) =∎
              ⟩
        ! (!-inv-r (! (ap [_]₂ (GH.η embase)))) ◃∙
        ! (ap (λ v → ! (ap [_]₂ (GH.η (−₁ (HG.cp₀₁ h v)))) ∙ ! (! (ap [_]₂ (GH.η embase)))) (emloop g)) ◃∙
        !-inv-r (! (ap [_]₂ (GH.η embase))) ◃∎
          =ₛ⟨ =ₛ-in {t = ! (!-inv-r (h₁' embase)) ◃∙
                         ! (ap (λ v → h₁' v ∙ ! (h₁' embase)) (emloop g)) ◃∙
                         !-inv-r (h₁' embase) ◃∎} $
              ap (λ f → ! (!-inv-r (f embase)) ∙
                        ! (ap (λ v → f v ∙ ! (f embase)) (emloop g)) ∙
                        !-inv-r (f embase))
                  (! (λ= h₁'-path)) ⟩
        ! (!-inv-r (h₁' embase)) ◃∙
        ! (ap (λ v → h₁' v ∙ ! (h₁' embase)) (emloop g)) ◃∙
        !-inv-r (h₁' embase) ◃∎ ∎ₛ
      transp-nat-idp : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A → B → C)
        {a₀ a₁ : A} (p : a₀ == a₁) (b : B)
        (c : C) (h₀ : ∀ b' → f a₀ b' == c)
        → app= (transp-naturality {B = λ a → ∀ b → f a b == c} (λ h → h b ∙ ! (h b)) p) h₀ ◃∎
          =ₛ
          !-inv-r (transport (λ a → ∀ b → f a b == c) p h₀ b) ◃∙
          ! (transp-idp (λ a → f a b) p) ◃∙
          ap (transport (λ a → f a b == f a b) p) (! (!-inv-r (h₀ b))) ◃∎
      transp-nat-idp f p@idp b c h₀ = !ₛ $
        !-inv-r (h₀ b) ◃∙
        idp ◃∙
        ap (λ r → r) (! (!-inv-r (h₀ b))) ◃∎
          =ₛ⟨ 1 & 1 & expand [] ⟩
        !-inv-r (h₀ b) ◃∙
        ap (λ r → r) (! (!-inv-r (h₀ b))) ◃∎
          =ₛ₁⟨ 1 & 1 & ap-idf (! (!-inv-r (h₀ b))) ⟩
        !-inv-r (h₀ b) ◃∙
        ! (!-inv-r (h₀ b)) ◃∎
          =ₛ₁⟨ !-inv-r (!-inv-r (h₀ b)) ⟩
        idp ◃∎ ∎ₛ
      top-part :
        ap-comm _G∪H_ (emloop g) (emloop h) ◃∙
        ap (_∙ ap (_G∪H embase) (emloop g)) (ap-cst [ north ] (emloop h)) ◃∙
        ap (idp ∙_) (GH.ap-cp₁₁-embase g) ◃∎
          =ₛ
        ap (ap (_G∪H embase) (emloop g) ∙_)
           (homotopy-to-cst-ap (λ y → [ north ]₂) h₁ (emloop h)) ◃∙
        ap (ap (_G∪H embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
        ap (_∙ idp) (GH.ap-cp₁₁-embase g) ◃∎
      top-part =
        ap-comm _G∪H_ (emloop g) (emloop h) ◃∙
        ap (_∙ ap (_G∪H embase) (emloop g)) (ap-cst [ north ] (emloop h)) ◃∙
        ap (idp ∙_) (GH.ap-cp₁₁-embase g) ◃∎
          =ₛ₁⟨ 1 & 1 &
               ap (ap (_∙ ap (_G∪H embase) (emloop g))) $ ! $
               cst-homotopy-to-cst-ap {A = EM₁ H.grp} {B = EMExplicit.EM G⊗H.abgroup 2}
                                              [ north ]₂ (emloop' H.grp h) ⟩
        ap-comm _G∪H_ (emloop g) (emloop h) ◃∙
        ap (_∙ ap (_G∪H embase) (emloop g))
           (homotopy-to-cst-ap (λ y → [ north ]₂) (λ y → idp) (emloop' H.grp h)) ◃∙
        ap (idp ∙_) (GH.ap-cp₁₁-embase g) ◃∎
          =ₛ⟨ 0 & 2 & post-rotate-out {r = _ ◃∙ _ ◃∙ _ ◃∎} $
                      ap-comm-cst-coh _G∪H_ (emloop g) (emloop h) [ north ]₂ (λ y → idp) ⟩
        ap (ap (_G∪H embase) (emloop g) ∙_)
           (homotopy-to-cst-ap (λ y → [ north ]₂) h₁ (emloop h)) ◃∙
        ap (ap (_G∪H embase) (emloop g) ∙_)
           (app= (transp-naturality {B = λ x → ∀ y → x G∪H y == [ north ]₂} {C = λ x → x G∪H embase == x G∪H embase}
                                    (λ h → h embase ∙ ! (h embase)) (emloop g))
                 (λ y → idp)) ◃∙
        ! (ap-transp (_G∪H embase) (_G∪H embase) (emloop g) idp) ◃∙
        ap (idp ∙_) (GH.ap-cp₁₁-embase g) ◃∎
          =ₛ⟨ 1 & 1 & ap-seq-=ₛ (ap (_G∪H embase) (emloop g) ∙_)
                                (transp-nat-idp _G∪H_ (emloop g) embase [ north ]₂ (λ y → idp)) ⟩
        ap (ap (_G∪H embase) (emloop g) ∙_)
           (homotopy-to-cst-ap (λ y → [ north ]₂) h₁ (emloop h)) ◃∙
        ap (ap (_G∪H embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
        ap (ap (_G∪H embase) (emloop g) ∙_)
            (! (transp-idp (_G∪H embase) (emloop g))) ◃∙
        idp ◃∙
        ! (ap-transp (_G∪H embase) (_G∪H embase) (emloop g) idp) ◃∙
        ap (idp ∙_) (GH.ap-cp₁₁-embase g) ◃∎
          =ₛ⟨ 3 & 1 & expand [] ⟩
        ap (ap (_G∪H embase) (emloop g) ∙_)
           (homotopy-to-cst-ap (λ y → [ north ]₂) h₁ (emloop h)) ◃∙
        ap (ap (_G∪H embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
        ap (ap (_G∪H embase) (emloop g) ∙_)
           (! (transp-idp (_G∪H embase) (emloop g))) ◃∙
        ! (ap-transp (_G∪H embase) (_G∪H embase) (emloop g) idp) ◃∙
        ap (idp ∙_) (GH.ap-cp₁₁-embase g) ◃∎
          =ₛ₁⟨ 2 & 1 & ap-! (ap (_G∪H embase) (emloop g) ∙_) (transp-idp (_G∪H embase) (emloop g)) ⟩
        ap (ap (_G∪H embase) (emloop g) ∙_)
           (homotopy-to-cst-ap (λ y → [ north ]₂) h₁ (emloop h)) ◃∙
        ap (ap (_G∪H embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
        ! (ap (ap (_G∪H embase) (emloop g) ∙_)
              (transp-idp (_G∪H embase) (emloop g))) ◃∙
        ! (ap-transp (_G∪H embase) (_G∪H embase) (emloop g) idp) ◃∙
        ap (idp ∙_) (GH.ap-cp₁₁-embase g) ◃∎
          =ₛ⟨ 2 & 2 & pre-rotate'-seq-in {p = _ ◃∙ _ ◃∎} {r = []} $
                      !ₛ $ ap-transp-idp (_G∪H embase) (emloop g) ⟩
        ap (ap (_G∪H embase) (emloop g) ∙_)
           (homotopy-to-cst-ap (λ y → [ north ]₂) h₁ (emloop h)) ◃∙
        ap (ap (_G∪H embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
        ∙-unit-r (ap (_G∪H embase) (emloop g)) ◃∙
        ap (idp ∙_) (GH.ap-cp₁₁-embase g) ◃∎
          =ₛ⟨ 2 & 2 & !ₛ $ homotopy-naturality (_∙ idp) (idp ∙_) ∙-unit-r (GH.ap-cp₁₁-embase g) ⟩
        ap (ap (_G∪H embase) (emloop g) ∙_)
           (homotopy-to-cst-ap (λ y → [ north ]₂) h₁ (emloop h)) ◃∙
        ap (ap (_G∪H embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
        ap (_∙ idp) (GH.ap-cp₁₁-embase g) ◃∙
        idp ◃∎
          =ₛ⟨ 3 & 1 & expand [] ⟩
        ap (ap (_G∪H embase) (emloop g) ∙_)
           (homotopy-to-cst-ap (λ y → [ north ]₂) h₁ (emloop h)) ◃∙
        ap (ap (_G∪H embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
        ap (_∙ idp) (GH.ap-cp₁₁-embase g) ◃∎ ∎ₛ
      bottom-part :
        ap (_∙ idp) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
        ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_) (! (!-inv-r (h₁' embase))) ◃∙
        ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_)
           (! (homotopy-to-cst-ap (λ x → [ north ]₂) h₁' (emloop g))) ◃∎
        =ₛ
        ap (idp ∙_) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
        ap (_∙ ap (λ y → − (y H∪G embase)) (emloop h)) (! (ap-cst [ north ]₂ (emloop g))) ◃∙
        ap-comm (λ x y → − (y H∪G x)) (emloop g) (emloop h) ◃∎
      bottom-part =
        ap (_∙ idp) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
        ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_) (! (!-inv-r (h₁' embase))) ◃∙
        ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_)
           (! (homotopy-to-cst-ap (λ x → [ north ]₂) h₁' (emloop g))) ◃∎
          =ₛ⟨ 0 & 0 & contract ⟩
        idp ◃∙
        ap (_∙ idp) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
        ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_) (! (!-inv-r (h₁' embase))) ◃∙
        ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_)
           (! (homotopy-to-cst-ap (λ x → [ north ]₂) h₁' (emloop g))) ◃∎
          =ₛ⟨ 0 & 2 & !ₛ (homotopy-naturality (idp ∙_) (_∙ idp) (! ∘ ∙-unit-r) (↯ (tail (comm-embase-emloop-seq h)))) ⟩
        ap (idp ∙_) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
        ! (∙-unit-r (ap (λ y → − (y H∪G embase)) (emloop h))) ◃∙
        ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_) (! (!-inv-r (h₁' embase))) ◃∙
        ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_)
           (! (homotopy-to-cst-ap (λ x → [ north ]₂) h₁' (emloop g))) ◃∎
          =ₛ⟨ 1 & 1 & !ₛ $ post-rotate-in {p = _ ◃∙ _ ◃∎} $
                      ap-transp-idp (λ y → − (y H∪G embase)) (emloop h) ⟩
        ap (idp ∙_) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
        ap-transp (λ y → − (y H∪G embase)) (λ y → − (y H∪G embase)) (emloop h) idp ◃∙
        ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_) (transp-idp (λ y → − (y H∪G embase)) (emloop h)) ◃∙
        ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_) (! (!-inv-r (h₁' embase))) ◃∙
        ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_)
           (! (homotopy-to-cst-ap (λ x → [ north ]₂) h₁' (emloop g))) ◃∎
          =ₛ⟨ 2 & 2 & ap-seq-=ₛ (ap (λ y → − (y H∪G embase)) (emloop h) ∙_) $
              transp-idp (λ y → − (y H∪G embase)) (emloop h) ◃∙
              ! (!-inv-r (h₁' embase)) ◃∎
                =ₛ⟨ pre-rotate-out $ pre-rotate'-in $ post-rotate-in {p = []} $
                    transp-nat-idp (λ y x → − (y H∪G x)) (emloop h) embase [ north ]₂ (λ x → idp) ⟩
              idp ◃∙
              ! (app= (transp-naturality {B = λ y → ∀ x → − (y H∪G x) == [ north ]₂}
                                          (λ h → h embase ∙ ! (h embase)) (emloop h))
                      (λ x → idp)) ◃∎
                =ₛ⟨ 0 & 1 & expand [] ⟩
              ! (app= (transp-naturality {B = λ y → ∀ x → − (y H∪G x) == [ north ]₂}
                                          (λ h → h embase ∙ ! (h embase)) (emloop h))
                      (λ x → idp)) ◃∎ ∎ₛ
            ⟩
        ap (idp ∙_) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
        ap-transp (λ y → − (y H∪G embase)) (λ y → − (y H∪G embase)) (emloop h) idp ◃∙
        ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_)
           (! (app= (transp-naturality {B = λ y → ∀ x → − (y H∪G x) == [ north ]₂}
                                        (λ h → h embase ∙ ! (h embase)) (emloop h))
                    (λ x → idp))) ◃∙
        ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_)
           (! (homotopy-to-cst-ap (λ x → [ north ]₂) h₁' (emloop g))) ◃∎
          =ₛ₁⟨ 2 & 1 & ap-! (ap (λ y → − (y H∪G embase)) (emloop h) ∙_)
                            (app= (transp-naturality {B = λ y → ∀ x → − (y H∪G x) == [ north ]₂}
                                                      (λ h → h embase ∙ ! (h embase)) (emloop h))
                                  (λ x → idp)) ⟩
        ap (idp ∙_) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
        ap-transp (λ y → − (y H∪G embase)) (λ y → − (y H∪G embase)) (emloop h) idp ◃∙
        ! (ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_)
              (app= (transp-naturality {B = λ y → ∀ x → − (y H∪G x) == [ north ]₂}
                                        (λ h → h embase ∙ ! (h embase)) (emloop h))
                    (λ x → idp))) ◃∙
        ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_)
           (! (homotopy-to-cst-ap (λ x → [ north ]₂) h₁' (emloop g))) ◃∎
          =ₛ₁⟨ 3 & 1 & ap-! (ap (λ y → − (y H∪G embase)) (emloop h) ∙_)
                            (homotopy-to-cst-ap (λ x → [ north ]₂) h₁' (emloop g)) ⟩
        ap (idp ∙_) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
        ap-transp (λ y → − (y H∪G embase)) (λ y → − (y H∪G embase)) (emloop h) idp ◃∙
        ! (ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_)
              (app= (transp-naturality {B = λ y → ∀ x → − (y H∪G x) == [ north ]₂}
                                        (λ h → h embase ∙ ! (h embase)) (emloop h))
                    (λ x → idp))) ◃∙
        ! (ap (ap (λ y → − (y H∪G embase)) (emloop h) ∙_)
              (homotopy-to-cst-ap (λ x → [ north ]₂) h₁' (emloop g))) ◃∎
          =ₛ⟨ 1 & 3 & pre-rotate-out $
                      pre-rotate'-seq-in {p = _ ◃∙ _ ◃∎} $
                      post-rotate-in {p = []} $
                      ap-comm-cst-coh (λ y x → − (y H∪G x))
                                      (emloop h) (emloop g) [ north ]₂ (λ x → idp) ⟩
        ap (idp ∙_) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
        ! (ap (_∙ ap (λ y → − (y H∪G embase)) (emloop h))
              (homotopy-to-cst-ap (λ x → − (embase H∪G x)) (λ x → idp) (emloop g))) ◃∙
        ! (ap-comm (λ y x → − (y H∪G x)) (emloop h) (emloop g)) ◃∎
          =ₛ₁⟨ 2 & 1 & ! (ap-comm-comm (λ x y → − (y H∪G x)) (emloop g) (emloop h)) ⟩
        ap (idp ∙_) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
        ! (ap (_∙ ap (λ y → − (y H∪G embase)) (emloop h))
              (homotopy-to-cst-ap (λ x → − (embase H∪G x)) (λ x → idp) (emloop g))) ◃∙
        ap-comm (λ x y → − (y H∪G x)) (emloop g) (emloop h) ◃∎
          =ₛ₁⟨ 1 & 1 &
                ! (ap (_∙ ap (λ y → − (y H∪G embase)) (emloop h))
                      (homotopy-to-cst-ap (λ x → − (embase H∪G x)) (λ x → idp) (emloop g)))
                  =⟨ !-ap (_∙ ap (λ y → − (y H∪G embase)) (emloop h))
                          (homotopy-to-cst-ap (λ x → − (embase H∪G x)) (λ x → idp) (emloop g)) ⟩
                ap (_∙ ap (λ y → − (y H∪G embase)) (emloop h))
                   (! (homotopy-to-cst-ap (λ x → − (embase H∪G x)) (λ x → idp) (emloop g)))
                  =⟨ ap (ap (_∙ ap (λ y → − (y H∪G embase)) (emloop h)) ∘ !) $
                     cst-homotopy-to-cst-ap [ north ]₂ (emloop g) ⟩
                ap (_∙ ap (λ y → − (y H∪G embase)) (emloop h)) (! (ap-cst [ north ]₂ (emloop g))) =∎
              ⟩
        ap (idp ∙_) (↯ (tail (comm-embase-emloop-seq h))) ◃∙
        ap (_∙ ap (λ y → − (y H∪G embase)) (emloop h)) (! (ap-cst [ north ]₂ (emloop g))) ◃∙
        ap-comm (λ x y → − (y H∪G x)) (emloop g) (emloop h) ◃∎ ∎ₛ
      step₄' : ! (ap-cst [ north ] (emloop g)) ◃∎
                =ₛ
                ↯ h₁'-seq ◃∙
                ! (!-inv-r (h₁' embase)) ◃∙
                ! (homotopy-to-cst-ap (λ x → [ north ]₂) h₁' (emloop g)) ◃∎
      step₄' = pre-rotate'-in $ post-rotate-seq-in {p = []} $ !ₛ $
        ap-cst [ north ]₂ (emloop g) ◃∙
        ↯ h₁'-seq ◃∎
          =ₛ⟨ 1 & 1 & expand h₁'-seq ⟩
        ap-cst [ north ] (emloop g) ◃∙
        ! (!-inv-r (h₁' embase)) ◃∙
        ! (ap (λ v → h₁' v ∙ ! (h₁' embase)) (emloop g)) ◃∙
        !-inv-r (h₁' embase) ◃∎
          =ₛ⟨ 0 & 2 & !ₛ $ post-rotate-in {p = _ ◃∙ _ ◃∎} $
                      cst-homotopy-to-cst-ap' [ north ]₂ [ north ]₂ h₁' (emloop g) ⟩
        homotopy-to-cst-ap (cst [ north ]₂) h₁' (emloop g) ◃∙
        ap (λ v → h₁' v ∙ ! (h₁' embase)) (emloop g) ◃∙
        ! (ap (λ v → h₁' v ∙ ! (h₁' embase)) (emloop g)) ◃∙
        !-inv-r (h₁' embase) ◃∎
          =ₛ⟨ 1 & 2 & seq-!-inv-r (ap (λ v → h₁' v ∙ ! (h₁' embase)) (emloop g) ◃∎) ⟩
        homotopy-to-cst-ap (cst [ north ]₂) h₁' (emloop g) ◃∙
        !-inv-r (h₁' embase) ◃∎ ∎ₛ
      step₁₃' :
        homotopy-to-cst-ap (λ y → [ north ]₂) h₁ (emloop h) ◃∙
        !-inv-r (h₁ embase) ◃∙
        ↯ h₁-seq ◃∎
        =ₛ
        ap-cst [ north ]₂ (emloop h) ◃∎
      step₁₃' =
        homotopy-to-cst-ap (λ y → [ north ]₂) h₁ (emloop h) ◃∙
        !-inv-r (h₁ embase) ◃∙
        ↯ h₁-seq ◃∎
          =ₛ⟨ 2 & 1 & expand h₁-seq ⟩
        homotopy-to-cst-ap (λ y → [ north ]₂) h₁ (emloop h) ◃∙
        !-inv-r (h₁ embase) ◃∙
        ! (!-inv-r (h₁ embase)) ◃∙
        ap (λ v → h₁ v ∙ ! (h₁ embase)) (emloop h) ◃∙
        !-inv-r (h₁ embase) ◃∎
          =ₛ⟨ 1 & 2 & seq-!-inv-r (!-inv-r (h₁ embase) ◃∎) ⟩
        homotopy-to-cst-ap (λ y → [ north ]₂) h₁ (emloop h) ◃∙
        ap (λ v → h₁ v ∙ ! (h₁ embase)) (emloop h) ◃∙
        !-inv-r (h₁ embase) ◃∎
          =ₛ⟨ cst-homotopy-to-cst-ap' [ north ]₂ [ north ]₂ h₁ (emloop h) ⟩
        ap-cst [ north ]₂ (emloop h) ◃∎ ∎ₛ

  comm-embase-emloop : ∀ h →
    Square idp
            (ap (embase G∪H_) (emloop h))
            (ap (λ y → − (y H∪G embase)) (emloop h))
            idp
  comm-embase-emloop h = vert-degen-square (comm-embase-emloop' h)

  comm-emloop-embase : ∀ g →
    Square idp
            (ap (_G∪H embase) (emloop g))
            (ap (λ x → − (embase H∪G x)) (emloop g))
            idp
  comm-emloop-embase g = vert-degen-square (comm-emloop-embase' g)

  abstract

    square-helper : ∀ {i} {A : Type i}
      {a a' a'' : A}
      {p₀ : a == a'} {q₀ : a' == a''} {r₀ : a == a''}
      {p₁ : a == a'} {q₁ : a' == a''} {r₁ : a == a''}
      (s : r₀ == p₀ ∙ q₀)
      (p : p₀ == p₁)
      (q : q₀ == q₁)
      (t : p₁ ∙ q₁ == r₁)
      → s ∙v⊡ (vert-degen-square p ⊡h vert-degen-square q) ⊡v∙ t ==
        vert-degen-square (s ∙ ap2 _∙_ p q ∙ t)
    square-helper s p q t =
      s ∙v⊡ (vert-degen-square p ⊡h vert-degen-square q) ⊡v∙ t
        =⟨ ap (λ u → s ∙v⊡ u ⊡v∙ t) (vert-degen-square-⊡h p q) ⟩
      s ∙v⊡ vert-degen-square (ap2 _∙_ p q) ⊡v∙ t
        =⟨ ap (s ∙v⊡_) (vert-degen-square-⊡v∙ (ap2 _∙_ p q) t) ⟩
      s ∙v⊡ vert-degen-square (ap2 _∙_ p q ∙ t)
        =⟨ vert-degen-square-∙v⊡ s (ap2 _∙_ p q ∙ t) ⟩
      vert-degen-square (s ∙ ap2 _∙_ p q ∙ t) =∎

    comm-embase-emloop-comp : ∀ h₁ h₂ →
      comm-embase-emloop (H.comp h₁ h₂) ⊡v∙
      ap (ap (λ y → − (y H∪G embase))) (emloop-comp h₁ h₂)
      ==
      ap (ap (embase G∪H_)) (emloop-comp h₁ h₂) ∙v⊡
      ↓-='-square-comp (comm-embase-emloop h₁) (comm-embase-emloop h₂)
    comm-embase-emloop-comp h₁ h₂ =
      comm-embase-emloop (H.comp h₁ h₂) ⊡v∙
      ap (ap (λ y → − (y H∪G embase))) (emloop-comp h₁ h₂)
        =⟨ vert-degen-square-⊡v∙
              (comm-embase-emloop' (H.comp h₁ h₂))
              (ap (ap (λ y → − (y H∪G embase))) (emloop-comp h₁ h₂)) ⟩
      vert-degen-square
        (comm-embase-emloop' (H.comp h₁ h₂) ∙
          ap (ap (λ y → − (y H∪G embase))) (emloop-comp h₁ h₂))
        =⟨ ap vert-degen-square (=ₛ-out (comm-embase-emloop-comp' h₁ h₂)) ⟩
      vert-degen-square
        (ap (ap (embase G∪H_)) (emloop-comp h₁ h₂) ∙
          ap-∙ (embase G∪H_) (emloop h₁) (emloop h₂) ∙
          ap2 _∙_ (comm-embase-emloop' h₁) (comm-embase-emloop' h₂) ∙
          ∙-ap (λ y → − (y H∪G embase)) (emloop h₁) (emloop h₂))
        =⟨ ! $ vert-degen-square-∙v⊡ (ap (ap (embase G∪H_)) (emloop-comp h₁ h₂)) _ ⟩
      ap (ap (embase G∪H_)) (emloop-comp h₁ h₂) ∙v⊡
      vert-degen-square
        (ap-∙ (embase G∪H_) (emloop h₁) (emloop h₂) ∙
          ap2 _∙_ (comm-embase-emloop' h₁) (comm-embase-emloop' h₂) ∙
          ∙-ap (λ y → − (y H∪G embase)) (emloop h₁) (emloop h₂))
        =⟨ ap (ap (ap (embase G∪H_)) (emloop-comp h₁ h₂) ∙v⊡_) $ ! $
           square-helper (ap-∙ (embase G∪H_) (emloop h₁) (emloop h₂))
                         (comm-embase-emloop' h₁) (comm-embase-emloop' h₂)
                         (∙-ap (λ y → − (y H∪G embase)) (emloop h₁) (emloop h₂)) ⟩
      ap (ap (embase G∪H_)) (emloop-comp h₁ h₂) ∙v⊡
      ↓-='-square-comp' (comm-embase-emloop h₁) (comm-embase-emloop h₂)
        =⟨ ap (ap (ap (embase G∪H_)) (emloop-comp h₁ h₂) ∙v⊡_) $
           ↓-='-square-comp'=↓-='-square-comp (comm-embase-emloop h₁)
                                              (comm-embase-emloop h₂) ⟩
      ap (ap (embase G∪H_)) (emloop-comp h₁ h₂) ∙v⊡
      ↓-='-square-comp (comm-embase-emloop h₁) (comm-embase-emloop h₂) =∎

    comm-emloop-comp-embase : ∀ g₁ g₂ →
      comm-emloop-embase (G.comp g₁ g₂) ⊡v∙
      ap (ap (λ x → − (embase H∪G x))) (emloop-comp g₁ g₂)
      ==
      ap (ap (_G∪H embase)) (emloop-comp g₁ g₂) ∙v⊡
      ↓-='-square-comp (comm-emloop-embase g₁) (comm-emloop-embase g₂)
    comm-emloop-comp-embase g₁ g₂ =
      comm-emloop-embase (G.comp g₁ g₂) ⊡v∙
      ap (ap (λ x → − (embase H∪G x))) (emloop-comp g₁ g₂)
        =⟨ vert-degen-square-⊡v∙
             (comm-emloop-embase' (G.comp g₁ g₂))
             (ap (ap (λ x → − (embase H∪G x))) (emloop-comp g₁ g₂)) ⟩
      vert-degen-square
        (comm-emloop-embase' (G.comp g₁ g₂) ∙
          ap (ap (λ x → − (embase H∪G x))) (emloop-comp g₁ g₂))
          =⟨ ap vert-degen-square (=ₛ-out (comm-emloop-comp-embase' g₁ g₂)) ⟩
      vert-degen-square
        (ap (ap (_G∪H embase)) (emloop-comp g₁ g₂) ∙
         ap-∙ (_G∪H embase) (emloop g₁) (emloop g₂) ∙
         ap2 _∙_ (comm-emloop-embase' g₁) (comm-emloop-embase' g₂) ∙
         ∙-ap (λ x → − (embase H∪G x)) (emloop g₁) (emloop g₂))
        =⟨ ! $ vert-degen-square-∙v⊡ (ap (ap (_G∪H embase)) (emloop-comp g₁ g₂)) _ ⟩
      ap (ap (_G∪H embase)) (emloop-comp g₁ g₂) ∙v⊡
      vert-degen-square
        (ap-∙ (_G∪H embase) (emloop g₁) (emloop g₂) ∙
         ap2 _∙_ (comm-emloop-embase' g₁) (comm-emloop-embase' g₂) ∙
         ∙-ap (λ x → − (embase H∪G x)) (emloop g₁) (emloop g₂))
        =⟨ ap (ap (ap (_G∪H embase)) (emloop-comp g₁ g₂) ∙v⊡_) $ ! $
           square-helper
             (ap-∙ (_G∪H embase) (emloop g₁) (emloop g₂))
             (comm-emloop-embase' g₁) (comm-emloop-embase' g₂)
             (∙-ap (λ x → − (embase H∪G x)) (emloop g₁) (emloop g₂)) ⟩
      ap (ap (_G∪H embase)) (emloop-comp g₁ g₂) ∙v⊡
      ↓-='-square-comp' (comm-emloop-embase g₁) (comm-emloop-embase g₂)
        =⟨ ap (ap (ap (_G∪H embase)) (emloop-comp g₁ g₂) ∙v⊡_) $
           ↓-='-square-comp'=↓-='-square-comp
             (comm-emloop-embase g₁) (comm-emloop-embase g₂) ⟩
      ap (ap (_G∪H embase)) (emloop-comp g₁ g₂) ∙v⊡
      ↓-='-square-comp (comm-emloop-embase g₁) (comm-emloop-embase g₂) =∎

    comm-emloop-emloop : ∀ g h →
      ap-comm _G∪H_ (emloop g) (emloop h) ∙v⊡
      comm-embase-emloop h ⊡h comm-emloop-embase g
      ==
      (comm-emloop-embase g ⊡h comm-embase-emloop h) ⊡v∙
      ap-comm (λ x y → − (y H∪G x)) (emloop g) (emloop h)
    comm-emloop-emloop g h =
      ap-comm _G∪H_ (emloop g) (emloop h) ∙v⊡
      comm-embase-emloop h ⊡h comm-emloop-embase g
        =⟨ ap (ap-comm _G∪H_ (emloop g) (emloop h) ∙v⊡_) $
           vert-degen-square-⊡h (comm-embase-emloop' h) (comm-emloop-embase' g) ⟩
      ap-comm _G∪H_ (emloop g) (emloop h) ∙v⊡
      vert-degen-square (ap2 _∙_ (comm-embase-emloop' h) (comm-emloop-embase' g))
        =⟨ vert-degen-square-∙v⊡ (ap-comm _G∪H_ (emloop g) (emloop h)) _ ⟩
      vert-degen-square
        (ap-comm _G∪H_ (emloop g) (emloop h) ∙
         ap2 _∙_ (comm-embase-emloop' h) (comm-emloop-embase' g))
        =⟨ ap vert-degen-square (=ₛ-out (comm-emloop-emloop' g h)) ⟩
      vert-degen-square
        (ap2 _∙_ (comm-emloop-embase' g) (comm-embase-emloop' h) ∙
         ap-comm (λ x y → − (y H∪G x)) (emloop g) (emloop h))
        =⟨ ! $ vert-degen-square-⊡v∙ _ (ap-comm (λ x y → − (y H∪G x)) (emloop g) (emloop h)) ⟩
      vert-degen-square (ap2 _∙_ (comm-emloop-embase' g) (comm-embase-emloop' h)) ⊡v∙
      ap-comm (λ x y → − (y H∪G x)) (emloop g) (emloop h)
        =⟨ ap (_⊡v∙ ap-comm (λ x y → − (y H∪G x)) (emloop g) (emloop h)) $ ! $
           vert-degen-square-⊡h (comm-emloop-embase' g) (comm-embase-emloop' h) ⟩
      (comm-emloop-embase g ⊡h comm-embase-emloop h) ⊡v∙
      ap-comm (λ x y → − (y H∪G x)) (emloop g) (emloop h) =∎

  module CP₁₁Comm =
    EM₁Level₂DoublePathElim G.grp H.grp {C = EMExplicit.EM G⊗H.abgroup 2} {{Trunc-level}}
      _G∪H_
      (λ x y → − (y H∪G x))
      idp
      comm-embase-emloop
      comm-emloop-embase
      comm-embase-emloop-comp
      comm-emloop-comp-embase
      comm-emloop-emloop

  abstract
    cp₁₁-comm : ∀ x y → x G∪H y == − (y H∪G x)
    cp₁₁-comm = CP₁₁Comm.f
