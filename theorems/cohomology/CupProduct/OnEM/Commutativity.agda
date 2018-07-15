{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane

module cohomology.CupProduct.OnEM.Commutativity {i} (R : CRing i) where

  open import cohomology.CupProduct.OnEM.Definition R
  open CP₁₁

  open EMExplicit R.add-ab-group

  EM₁-antipodal-map : EM₁ R₊ → EM₁ R₊
  EM₁-antipodal-map = EM₁-fmap (inv-hom R.add-ab-group)

  ⊙EM₁-antipodal-map : ⊙EM₁ R₊ ⊙→ ⊙EM₁ R₊
  ⊙EM₁-antipodal-map = EM₁-antipodal-map , idp

  EM₁-antipodal-map-! : ∀ g → ap EM₁-antipodal-map (emloop g) == ! (emloop g)
  EM₁-antipodal-map-! g =
    ap EM₁-antipodal-map (emloop g)
      =⟨ EM₁-fmap-emloop-β (inv-hom R.add-ab-group) g ⟩
    emloop (R.neg g)
      =⟨ emloop-inv g ⟩
    ! (emloop g) =∎

  antipodal-map : EM 2 → EM 2
  antipodal-map = Trunc-fmap (Susp-fmap EM₁-antipodal-map)

  module CP₀₁-comm where

    cp₀₁-comm : ∀ g h → ap (cp₀₁ g) (emloop h) == ap (cp₀₁ h) (emloop g)
    cp₀₁-comm g h =
      ap (cp₀₁ g) (emloop h)
        =⟨ cp₀₁-emloop-β g h ⟩
      emloop (R.mult g h)
        =⟨ ap emloop (R.mult-comm g h) ⟩
      emloop (R.mult h g)
        =⟨ ! (cp₀₁-emloop-β h g) ⟩
      ap (cp₀₁ h) (emloop g) =∎

  module CP₁₁-comm where

    abstract

      comm-embase-emloop↯ : ∀ h →
        ap (λ y → cp₁₁ embase y) (emloop h) =-=
        ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h)
      comm-embase-emloop↯ h =
        ap (λ y → cp₁₁ embase y) (emloop h)
          =⟪idp⟫
        ap (cst [ north ]) (emloop h)
          =⟪ ap-cst [ north ] (emloop h) ⟫
        idp
          =⟪idp⟫
        ap antipodal-map (idp {a = [ north ]})
          =⟪ ! (ap (ap antipodal-map) (ap-cp₁₁-embase h)) ⟫
        ap antipodal-map (ap (λ y → cp₁₁ y embase) (emloop h))
          =⟪ ∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop h) ⟫
        ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∎∎

      comm-emloop-embase↯ : ∀ g →
        ap (λ x → cp₁₁ x embase) (emloop g) =-=
        ap (antipodal-map ∘ cp₁₁ embase) (emloop g)
      comm-emloop-embase↯ g =
        ap (λ x → cp₁₁ x embase) (emloop g)
          =⟪ ap-cp₁₁-embase g ⟫
        idp
          =⟪ ! (ap-cst [ north ] (emloop g)) ⟫
        ap (cst [ north ]) (emloop g)
          =⟪idp⟫
        ap (antipodal-map ∘ cp₁₁ embase) (emloop g) ∎∎

      comm-embase-emloop' : ∀ h →
        ap (λ y → cp₁₁ embase y) (emloop h) ==
        ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h)
      comm-embase-emloop' h = ↯ (comm-embase-emloop↯ h)

      comm-emloop-embase' : ∀ g →
        ap (λ x → cp₁₁ x embase) (emloop g) ==
        ap (λ x → antipodal-map (cp₁₁ embase x)) (emloop g)
      comm-emloop-embase' g = ↯ (comm-emloop-embase↯ g)

      comm-embase-emloop-comp' : ∀ h₁ h₂ →
        comm-embase-emloop' (R.add h₁ h₂) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase))) (emloop-comp h₁ h₂) ◃∎
        =ₛ
        ap (ap (λ y → cp₁₁ embase y)) (emloop-comp h₁ h₂) ◃∙
        ap-∙ (λ y → cp₁₁ embase y) (emloop h₁) (emloop h₂) ◃∙
        ap2 _∙_ (comm-embase-emloop' h₁) (comm-embase-emloop' h₂) ◃∙
        ∙-ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h₁) (emloop h₂) ◃∎
      comm-embase-emloop-comp' h₁ h₂ =
        comm-embase-emloop' (R.add h₁ h₂) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase))) (emloop-comp h₁ h₂) ◃∎
          =ₛ⟨ 0 & 1 & expand (comm-embase-emloop↯ (R.add h₁ h₂)) ⟩
        ap-cst [ north ] (emloop (R.add h₁ h₂)) ◃∙
        ! (ap (ap antipodal-map) (ap-cp₁₁-embase (R.add h₁ h₂))) ◃∙
        ∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop (R.add h₁ h₂)) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase))) (emloop-comp h₁ h₂) ◃∎
          =ₛ⟨ 2 & 2 & !ₛ $
              homotopy-naturality (ap antipodal-map ∘ ap (λ y → cp₁₁ y embase))
                                  (ap (λ y → antipodal-map (cp₁₁ y embase)))
                                  (∘-ap antipodal-map (λ y → cp₁₁ y embase))
                                  (emloop-comp h₁ h₂) ⟩
        ap-cst [ north ] (emloop (R.add h₁ h₂)) ◃∙
        ! (ap (ap antipodal-map) (ap-cp₁₁-embase (R.add h₁ h₂))) ◃∙
        ap (ap antipodal-map ∘ ap (λ y → cp₁₁ y embase)) (emloop-comp h₁ h₂) ◃∙
        ∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop h₁ ∙ emloop h₂) ◃∎
          =ₛ₁⟨ 1 & 1 & !-ap (ap antipodal-map) (ap-cp₁₁-embase (R.add h₁ h₂)) ⟩
        ap-cst [ north ] (emloop (R.add h₁ h₂)) ◃∙
        ap (ap antipodal-map) (! (ap-cp₁₁-embase (R.add h₁ h₂))) ◃∙
        ap (ap antipodal-map ∘ ap (λ y → cp₁₁ y embase)) (emloop-comp h₁ h₂) ◃∙
        ∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop h₁ ∙ emloop h₂) ◃∎
          =ₛ₁⟨ 2 & 1 & ap-∘ (ap antipodal-map) (ap (λ y → cp₁₁ y embase)) (emloop-comp h₁ h₂) ⟩
        ap-cst [ north ] (emloop (R.add h₁ h₂)) ◃∙
        ap (ap antipodal-map) (! (ap-cp₁₁-embase (R.add h₁ h₂))) ◃∙
        ap (ap antipodal-map) (ap (ap (λ y → cp₁₁ y embase)) (emloop-comp h₁ h₂)) ◃∙
        ∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop h₁ ∙ emloop h₂) ◃∎
          =ₛ⟨ 1 & 2 &
              ap-seq-=ₛ (ap antipodal-map) $
              post-rotate-seq-in {p = _ ◃∙ _ ◃∎} $
              pre-rotate'-in $
              !ₛ $ ap-cp₁₁-embase-coh h₁ h₂ ⟩
        ap-cst [ north ] (emloop (R.add h₁ h₂)) ◃∙
        ap (ap antipodal-map) (! (ap2 _∙_ (ap-cp₁₁-embase h₁) (ap-cp₁₁-embase h₂))) ◃∙
        ap (ap antipodal-map) (! (ap-∙ (λ x → cp₁₁ x embase) (emloop h₁) (emloop h₂))) ◃∙
        ∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop h₁ ∙ emloop h₂) ◃∎
          =ₛ₁⟨ 2 & 1 & ap-! (ap antipodal-map) (ap-∙ (λ x → cp₁₁ x embase) (emloop h₁) (emloop h₂))⟩
        ap-cst [ north ] (emloop (R.add h₁ h₂)) ◃∙
        ap (ap antipodal-map) (! (ap2 _∙_ (ap-cp₁₁-embase h₁) (ap-cp₁₁-embase h₂))) ◃∙
        ! (ap (ap antipodal-map) (ap-∙ (λ x → cp₁₁ x embase) (emloop h₁) (emloop h₂))) ◃∙
        ∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop h₁ ∙ emloop h₂) ◃∎
          =ₛ₁⟨ 3 & 1 & ! (!ap-∘=∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop h₁ ∙ emloop h₂)) ⟩
        ap-cst [ north ] (emloop (R.add h₁ h₂)) ◃∙
        ap (ap antipodal-map) (! (ap2 _∙_ (ap-cp₁₁-embase h₁) (ap-cp₁₁-embase h₂))) ◃∙
        ! (ap (ap antipodal-map) (ap-∙ (λ x → cp₁₁ x embase) (emloop h₁) (emloop h₂))) ◃∙
        ! (ap-∘ antipodal-map (λ y → cp₁₁ y embase) (emloop h₁ ∙ emloop h₂)) ◃∎
          =ₛ⟨ 2 & 2 &
              post-rotate-seq-in {p = ! (ap (ap antipodal-map) (ap-∙ (λ x → cp₁₁ x embase) (emloop h₁) (emloop h₂))) ◃∙
                                      ! (ap-∘ antipodal-map (λ y → cp₁₁ y embase) (emloop h₁ ∙ emloop h₂)) ◃∎} $
              pre-rotate'-seq-in {p = ap-∘ antipodal-map (λ y → cp₁₁ y embase) (emloop h₁ ∙ emloop h₂) ◃∙
                                      ap (ap antipodal-map) (ap-∙ (λ x → cp₁₁ x embase) (emloop h₁) (emloop h₂)) ◃∎} $
              ap-∘-∙-coh antipodal-map (λ y → cp₁₁ y embase) (emloop h₁) (emloop h₂) ⟩
        ap-cst [ north ] (emloop (R.add h₁ h₂)) ◃∙
        ap (ap antipodal-map) (! (ap2 _∙_ (ap-cp₁₁-embase h₁) (ap-cp₁₁-embase h₂))) ◃∙
        ap-∙ antipodal-map (ap (λ y → cp₁₁ y embase) (emloop h₁)) (ap (λ y → cp₁₁ y embase) (emloop h₂)) ◃∙
        ! (ap2 _∙_ (ap-∘ antipodal-map (λ y → cp₁₁ y embase) (emloop h₁))
                   (ap-∘ antipodal-map (λ y → cp₁₁ y embase) (emloop h₂))) ◃∙
        ! (ap-∙ (λ y → antipodal-map (cp₁₁ y embase)) (emloop h₁) (emloop h₂)) ◃∎
          =ₛ₁⟨ 1 & 1 &
               ap (ap (ap antipodal-map)) (!-ap2 _∙_ (ap-cp₁₁-embase h₁) (ap-cp₁₁-embase h₂)) ∙
               ap-ap2 (ap antipodal-map) _∙_ (! (ap-cp₁₁-embase h₁)) (! (ap-cp₁₁-embase h₂)) ⟩
        ap-cst [ north ] (emloop (R.add h₁ h₂)) ◃∙
        ap2 (λ p q → ap antipodal-map (p ∙ q)) (! (ap-cp₁₁-embase h₁)) (! (ap-cp₁₁-embase h₂)) ◃∙
        ap-∙ antipodal-map (ap (λ y → cp₁₁ y embase) (emloop h₁)) (ap (λ y → cp₁₁ y embase) (emloop h₂)) ◃∙
        ! (ap2 _∙_ (ap-∘ antipodal-map (λ y → cp₁₁ y embase) (emloop h₁))
                   (ap-∘ antipodal-map (λ y → cp₁₁ y embase) (emloop h₂))) ◃∙
        ! (ap-∙ (λ y → antipodal-map (cp₁₁ y embase)) (emloop h₁) (emloop h₂)) ◃∎
          =ₛ⟨ 1 & 2 &
              homotopy-naturality2 (λ p q → ap antipodal-map (p ∙ q))
                                   (λ p q → ap antipodal-map p ∙ ap antipodal-map q)
                                   (λ p q → ap-∙ antipodal-map p q)
                                   (! (ap-cp₁₁-embase h₁))
                                   (! (ap-cp₁₁-embase h₂)) ⟩
        ap-cst [ north ] (emloop (R.add h₁ h₂)) ◃∙
        idp ◃∙
        ap2 (λ p q → ap antipodal-map p ∙ ap antipodal-map q) (! (ap-cp₁₁-embase h₁)) (! (ap-cp₁₁-embase h₂)) ◃∙
        ! (ap2 _∙_ (ap-∘ antipodal-map (λ y → cp₁₁ y embase) (emloop h₁))
                   (ap-∘ antipodal-map (λ y → cp₁₁ y embase) (emloop h₂))) ◃∙
        ! (ap-∙ (λ y → antipodal-map (cp₁₁ y embase)) (emloop h₁) (emloop h₂)) ◃∎
          =ₛ⟨ 1 & 1 & expand [] ⟩
        ap-cst [ north ] (emloop (R.add h₁ h₂)) ◃∙
        ap2 (λ p q → ap antipodal-map p ∙ ap antipodal-map q) (! (ap-cp₁₁-embase h₁)) (! (ap-cp₁₁-embase h₂)) ◃∙
        ! (ap2 _∙_ (ap-∘ antipodal-map (λ y → cp₁₁ y embase) (emloop h₁))
                   (ap-∘ antipodal-map (λ y → cp₁₁ y embase) (emloop h₂))) ◃∙
        ! (ap-∙ (λ y → antipodal-map (cp₁₁ y embase)) (emloop h₁) (emloop h₂)) ◃∎
          =ₛ₁⟨ 1 & 1 &
               ! (ap2-ap-lr _∙_ (ap antipodal-map) (ap antipodal-map) (! (ap-cp₁₁-embase h₁)) (! (ap-cp₁₁-embase h₂))) ∙
               ap2 (ap2 _∙_) (ap-! (ap antipodal-map) (ap-cp₁₁-embase h₁)) (ap-! (ap antipodal-map) (ap-cp₁₁-embase h₂)) ⟩
        ap-cst [ north ] (emloop (R.add h₁ h₂)) ◃∙
        ap2 _∙_ (! (ap (ap antipodal-map) (ap-cp₁₁-embase h₁))) (! (ap (ap antipodal-map) (ap-cp₁₁-embase h₂))) ◃∙
        ! (ap2 _∙_ (ap-∘ antipodal-map (λ y → cp₁₁ y embase) (emloop h₁))
                   (ap-∘ antipodal-map (λ y → cp₁₁ y embase) (emloop h₂))) ◃∙
        ! (ap-∙ (λ y → antipodal-map (cp₁₁ y embase)) (emloop h₁) (emloop h₂)) ◃∎
          =ₛ₁⟨ 2 & 1 &
              !-ap2 _∙_ (ap-∘ antipodal-map (λ y → cp₁₁ y embase) (emloop h₁))
                        (ap-∘ antipodal-map (λ y → cp₁₁ y embase) (emloop h₂)) ∙
              ap2 (ap2 _∙_) (!ap-∘=∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop h₁))
                            (!ap-∘=∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop h₂)) ⟩
        ap-cst [ north ] (emloop (R.add h₁ h₂)) ◃∙
        ap2 _∙_ (! (ap (ap antipodal-map) (ap-cp₁₁-embase h₁))) (! (ap (ap antipodal-map) (ap-cp₁₁-embase h₂))) ◃∙
        ap2 _∙_ (∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop h₁))
                (∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop h₂)) ◃∙
        ! (ap-∙ (λ y → antipodal-map (cp₁₁ y embase)) (emloop h₁) (emloop h₂)) ◃∎
          =ₛ₁⟨ 3 & 1 & !ap-∙=∙-ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h₁) (emloop h₂) ⟩
        ap-cst [ north ] (emloop (R.add h₁ h₂)) ◃∙
        ap2 _∙_ (! (ap (ap antipodal-map) (ap-cp₁₁-embase h₁))) (! (ap (ap antipodal-map) (ap-cp₁₁-embase h₂))) ◃∙
        ap2 _∙_ (∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop h₁))
                (∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop h₂)) ◃∙
        ∙-ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h₁) (emloop h₂) ◃∎
          =ₛ⟨ 0 & 1 &
              ap-cst [ north ] (emloop (R.add h₁ h₂)) ◃∎
                =ₛ⟨ 1 & 0 & contract ⟩
              ap-cst [ north ] (emloop (R.add h₁ h₂)) ◃∙
              idp ◃∎
                =ₛ₁⟨ 1 & 1 & ! (ap-cst idp (emloop-comp h₁ h₂)) ⟩
              ap-cst [ north ] (emloop (R.add h₁ h₂)) ◃∙
              ap (λ _ → idp) (emloop-comp h₁ h₂) ◃∎
                =ₛ⟨ !ₛ (homotopy-naturality (ap (cp₁₁ embase)) (λ _ → idp) (ap-cst [ north ]) (emloop-comp h₁ h₂)) ⟩
              ap (ap (cp₁₁ embase)) (emloop-comp h₁ h₂) ◃∙
              ap-cst [ north ] (emloop h₁ ∙ emloop h₂) ◃∎
                =ₛ⟨ 1 & 1 & ap-cst-coh [ north ] (emloop h₁) (emloop h₂) ⟩
              ap (ap (cp₁₁ embase)) (emloop-comp h₁ h₂) ◃∙
              ap-∙ (cst [ north ]) (emloop h₁) (emloop h₂) ◃∙
              ap2 _∙_ (ap-cst [ north ] (emloop h₁)) (ap-cst [ north ] (emloop h₂)) ◃∎ ∎ₛ
            ⟩
        ap (ap (cp₁₁ embase)) (emloop-comp h₁ h₂) ◃∙
        ap-∙ (cst [ north ]) (emloop h₁) (emloop h₂) ◃∙
        ap2 _∙_ (ap-cst [ north ] (emloop h₁)) (ap-cst [ north ] (emloop h₂)) ◃∙
        ap2 _∙_ (! (ap (ap antipodal-map) (ap-cp₁₁-embase h₁))) (! (ap (ap antipodal-map) (ap-cp₁₁-embase h₂))) ◃∙
        ap2 _∙_ (∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop h₁))
                (∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop h₂)) ◃∙
        ∙-ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h₁) (emloop h₂) ◃∎
          =ₛ⟨ 2 & 3 & ∙-ap2-seq _∙_ (comm-embase-emloop↯ h₁) (comm-embase-emloop↯ h₂) ⟩
        ap (ap (λ y → cp₁₁ embase y)) (emloop-comp h₁ h₂) ◃∙
        ap-∙ (λ y → cp₁₁ embase y) (emloop h₁) (emloop h₂) ◃∙
        ap2 _∙_ (comm-embase-emloop' h₁) (comm-embase-emloop' h₂) ◃∙
        ∙-ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h₁) (emloop h₂) ◃∎ ∎ₛ

      comm-emloop-comp-embase' : ∀ g₁ g₂ →
        comm-emloop-embase' (R.add g₁ g₂) ◃∙
        ap (ap (λ x → antipodal-map (cp₁₁ embase x))) (emloop-comp g₁ g₂) ◃∎
        =ₛ
        ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ◃∙
        ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂) ◃∙
        ap2 _∙_ (comm-emloop-embase' g₁) (comm-emloop-embase' g₂) ◃∙
        ∙-ap (λ x → antipodal-map (cp₁₁ embase x)) (emloop g₁) (emloop g₂) ◃∎
      comm-emloop-comp-embase' g₁ g₂ =
        comm-emloop-embase' (R.add g₁ g₂) ◃∙
        ap (ap (λ x → antipodal-map (cp₁₁ embase x))) (emloop-comp g₁ g₂) ◃∎
          =ₛ⟨ 0 & 1 & expand (comm-emloop-embase↯ (R.add g₁ g₂)) ⟩
        ap-cp₁₁-embase (R.add g₁ g₂) ◃∙
        ! (ap-cst [ north ] (emloop (R.add g₁ g₂))) ◃∙
        ap (ap (λ x → antipodal-map (cp₁₁ embase x))) (emloop-comp g₁ g₂) ◃∎
          =ₛ⟨ 1 & 2 & !ₛ $
              homotopy-naturality
                (λ _ → idp)
                (ap (cst [ north ]))
                (λ p → ! (ap-cst [ north ] p))
                (emloop-comp g₁ g₂) ⟩
        ap-cp₁₁-embase (R.add g₁ g₂) ◃∙
        ap (λ _ → idp) (emloop-comp g₁ g₂) ◃∙
        ! (ap-cst [ north ] (emloop g₁ ∙ emloop g₂)) ◃∎
          =ₛ⟨ 1 & 1 & =ₛ-in {t = []} (ap-cst idp (emloop-comp g₁ g₂)) ⟩
        ap-cp₁₁-embase (R.add g₁ g₂) ◃∙
        ! (ap-cst [ north ] (emloop g₁ ∙ emloop g₂)) ◃∎
          =ₛ⟨ 0 & 1 & ap-cp₁₁-embase-coh g₁ g₂ ⟩
        ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ◃∙
        ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂) ◃∙
        ap2 _∙_ (ap-cp₁₁-embase g₁) (ap-cp₁₁-embase g₂) ◃∙
        ! (ap-cst [ north ] (emloop g₁ ∙ emloop g₂)) ◃∎
          =ₛ⟨ 3 & 1 & !-=ₛ $ ap-cst-coh [ north ] (emloop g₁) (emloop g₂) ⟩
        ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ◃∙
        ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂) ◃∙
        ap2 _∙_ (ap-cp₁₁-embase g₁) (ap-cp₁₁-embase g₂) ◃∙
        ! (ap2 _∙_ (ap-cst [ north ] (emloop g₁)) (ap-cst [ north ] (emloop g₂))) ◃∙
        ! (ap-∙ (cst [ north ]) (emloop g₁) (emloop g₂)) ◃∎
          =ₛ₁⟨ 3 & 1 & ! (ap2-! _∙_ (ap-cst [ north ] (emloop g₁)) (ap-cst [ north ] (emloop g₂))) ⟩
        ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ◃∙
        ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂) ◃∙
        ap2 _∙_ (ap-cp₁₁-embase g₁) (ap-cp₁₁-embase g₂) ◃∙
        ap2 _∙_ (! (ap-cst [ north ] (emloop g₁))) (! (ap-cst [ north ] (emloop g₂))) ◃∙
        ! (ap-∙ (cst [ north ]) (emloop g₁) (emloop g₂)) ◃∎
          =ₛ⟨ 2 & 2 & ∙-ap2-seq _∙_ (comm-emloop-embase↯ g₁) (comm-emloop-embase↯ g₂) ⟩
        ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ◃∙
        ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂) ◃∙
        ap2 _∙_ (comm-emloop-embase' g₁) (comm-emloop-embase' g₂) ◃∙
        ! (ap-∙ (cst [ north ]) (emloop g₁) (emloop g₂)) ◃∎
          =ₛ₁⟨ 3 & 1 & !ap-∙=∙-ap (cst [ north ]) (emloop g₁) (emloop g₂) ⟩
        ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ◃∙
        ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂) ◃∙
        ap2 _∙_ (comm-emloop-embase' g₁) (comm-emloop-embase' g₂) ◃∙
        ∙-ap (cst [ north ]) (emloop g₁) (emloop g₂) ◃∎ ∎ₛ

      comm-emloop-emloop' : ∀ g h →
        ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h) ◃∙
        ap2 _∙_ (comm-embase-emloop' h) (comm-emloop-embase' g) ◃∎
        =ₛ
        ap2 _∙_ (comm-emloop-embase' g) (comm-embase-emloop' h) ◃∙
        ap-comm (λ x y → antipodal-map (cp₁₁ y x)) (emloop g) (emloop h) ◃∎
      comm-emloop-emloop' g h =
        ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h) ◃∙
        ap2 _∙_ (comm-embase-emloop' h) (comm-emloop-embase' g) ◃∎
          =ₛ⟨ 1 & 1 & ap2-out _∙_ (comm-embase-emloop' h) (comm-emloop-embase' g) ⟩
        ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (comm-embase-emloop' h) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (comm-emloop-embase' g) ◃∎
          =ₛ⟨ 1 & 1 & ap-seq-=ₛ (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (take-drop-split 1 (comm-embase-emloop↯ h)) ⟩
        ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (ap-cst [ north ] (emloop h)) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (comm-emloop-embase' g) ◃∎
          =ₛ⟨ 3 & 1 & ap-seq-∙ (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (comm-emloop-embase↯ g) ⟩
        ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (ap-cst [ north ] (emloop h)) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (ap-cp₁₁-embase g) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (! (ap-cst [ north ] (emloop g))) ◃∎
          =ₛ⟨ 4 & 1 & ap-seq-=ₛ (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) step₄' ⟩
        ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (ap-cst [ north ] (emloop h)) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (ap-cp₁₁-embase g) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (↯ h₁'-seq) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (! (!-inv-r (h₁' embase))) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_)
           (! (homotopy-naturality-to-cst (λ x → [ north ]₂) [ north ]₂ h₁' (emloop g))) ◃∎
          =ₛ⟨ 2 & 2 & ap-comm-=ₛ _∙_ (↯ (tail (comm-embase-emloop↯ h))) (ap-cp₁₁-embase g) ⟩
        ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (ap-cst [ north ] (emloop h)) ◃∙
        ap (idp ∙_) (ap-cp₁₁-embase g) ◃∙
        ap (_∙ idp) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (↯ h₁'-seq) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (! (!-inv-r (h₁' embase))) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_)
           (! (homotopy-naturality-to-cst (λ x → [ north ]₂) [ north ]₂ h₁' (emloop g))) ◃∎
          =ₛ⟨ 3 & 2 & ap-comm-=ₛ _∙_ (↯ (tail (comm-embase-emloop↯ h))) (↯ h₁'-seq) ⟩
        ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (ap-cst [ north ] (emloop h)) ◃∙
        ap (idp ∙_) (ap-cp₁₁-embase g) ◃∙
        ap (idp ∙_) (↯ h₁'-seq) ◃∙
        ap (λ a → a ∙ idp) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (! (!-inv-r (h₁' embase))) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_)
           (! (homotopy-naturality-to-cst (λ x → [ north ]₂) [ north ]₂ h₁' (emloop g))) ◃∎
          =ₛ₁⟨ 3 & 1 & ap (ap (idp ∙_)) (! (=ₛ-out heart))⟩
        ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (ap-cst [ north ] (emloop h)) ◃∙
        ap (idp ∙_) (ap-cp₁₁-embase g) ◃∙
        ap (idp ∙_) (↯ h₁-seq) ◃∙
        ap (λ a → a ∙ idp) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (! (!-inv-r (h₁' embase))) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_)
           (! (homotopy-naturality-to-cst (λ x → [ north ]₂) [ north ]₂ h₁' (emloop g))) ◃∎
          =ₛ⟨ 0 & 3 & top-part ⟩
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_)
           (homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h)) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
        ap (_∙ idp) (ap-cp₁₁-embase g) ◃∙
        ap (idp ∙_) (↯ h₁-seq) ◃∙
        ap (λ a → a ∙ idp) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (! (!-inv-r (h₁' embase))) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_)
           (! (homotopy-naturality-to-cst (λ x → [ north ]₂) [ north ]₂ h₁' (emloop g))) ◃∎
          =ₛ⟨ 4 & 3 & bottom-part ⟩
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_)
           (homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h)) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
        ap (_∙ idp) (ap-cp₁₁-embase g) ◃∙
        ap (idp ∙_) (↯ h₁-seq) ◃∙
        ap (idp ∙_) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
        ap (_∙ ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h)) (! (ap-cst [ north ]₂ (emloop g))) ◃∙
        ap-comm (λ x y → antipodal-map (cp₁₁ y x)) (emloop g) (emloop h) ◃∎
          =ₛ⟨ 2 & 2 & ap-comm-=ₛ _∙_ (ap-cp₁₁-embase g) (↯ h₁-seq) ⟩
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_)
           (homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h)) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (↯ h₁-seq) ◃∙
        ap (_∙ idp) (ap-cp₁₁-embase g) ◃∙
        ap (idp ∙_) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
        ap (_∙ ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h)) (! (ap-cst [ north ]₂ (emloop g))) ◃∙
        ap-comm (λ x y → antipodal-map (cp₁₁ y x)) (emloop g) (emloop h) ◃∎
          =ₛ⟨ 3 & 2 & ap-comm-=ₛ _∙_ (ap-cp₁₁-embase g) (↯ (tail (comm-embase-emloop↯ h))) ⟩
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_)
           (homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h)) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (↯ h₁-seq) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
        ap (_∙ ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h)) (ap-cp₁₁-embase g) ◃∙
        ap (_∙ ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h)) (! (ap-cst [ north ]₂ (emloop g))) ◃∙
        ap-comm (λ x y → antipodal-map (cp₁₁ y x)) (emloop g) (emloop h) ◃∎
          =ₛ⟨ 4 & 2 & ∙-ap-seq (_∙ ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h)) (comm-emloop-embase↯ g) ⟩
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_)
           (homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h)) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (↯ h₁-seq) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
        ap (_∙ ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h)) (comm-emloop-embase' g) ◃∙
        ap-comm (λ x y → antipodal-map (cp₁₁ y x)) (emloop g) (emloop h) ◃∎
          =ₛ⟨ 0 & 3 & ap-seq-=ₛ (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) step₁₃' ⟩
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (ap-cst [ north ]₂ (emloop h)) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
        ap (_∙ ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h)) (comm-emloop-embase' g) ◃∙
        ap-comm (λ x y → antipodal-map (cp₁₁ y x)) (emloop g) (emloop h) ◃∎
          =ₛ⟨ 0 & 2 & !ₛ $ ap-seq-=ₛ (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) $
                      take-drop-split 1 (comm-embase-emloop↯ h) ⟩
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (comm-embase-emloop' h) ◃∙
        ap (_∙ ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h)) (comm-emloop-embase' g) ◃∙
        ap-comm (λ x y → antipodal-map (cp₁₁ y x)) (emloop g) (emloop h) ◃∎
          =ₛ⟨ 0 & 2 & !ₛ (ap2-out' _∙_ (comm-emloop-embase' g) (comm-embase-emloop' h)) ⟩
        ap2 _∙_ (comm-emloop-embase' g) (comm-embase-emloop' h) ◃∙
        ap-comm (λ x y → antipodal-map (cp₁₁ y x)) (emloop g) (emloop h) ◃∎ ∎ₛ
        where
        h₀ : ∀ y → cp₁₁ embase y == [ north ]₂
        h₀ y = idp
        h₁ : ∀ y → cp₁₁ embase y == [ north ]₂
        h₁ = transport (λ x → ∀ y → cp₁₁ x y == [ north ]₂) (emloop g) h₀
        h₀' : ∀ x → antipodal-map (cp₁₁ embase x) == [ north ]₂
        h₀' x = idp
        h₁' : ∀ x → antipodal-map (cp₁₁ embase x) == [ north ]₂
        h₁' = transport (λ y → ∀ x → antipodal-map (cp₁₁ y x) == [ north ]₂) (emloop h) h₀'
        h₁-path : ∀ y → h₁ y == ! (ap [_]₂ (η (cp₀₁ g y)))
        h₁-path y =
          transport (λ x → ∀ y → cp₁₁ x y == [ north ]₂) (emloop g) h₀ y
            =⟨ app= (Π-transp (emloop g) h₀) y ⟩
          transport (λ x → cp₁₁ x y == [ north ]₂) (emloop g) (h₀ y)
            =⟨ to-transp {B = λ x → cp₁₁ x y == [ north ]₂} {p = emloop g} $
               ↓-app=cst-in' {f = λ x → cp₁₁ x y} {p = emloop g} {u = idp} {v = ! (ap (λ x → cp₁₁ x y) (emloop g))} $
               ! (!-inv-r (ap (λ x → cp₁₁ x y) (emloop g))) ∙
               ∙=∙' (ap (λ x → cp₁₁ x y) (emloop g)) (! (ap (λ x → cp₁₁ x y) (emloop g))) ⟩
          ! (ap (λ x → cp₁₁ x y) (emloop g))
            =⟨ ap ! (ap-cp₁₁ g y) ⟩
          ! (ap [_] (η (cp₀₁ g y))) =∎
        h₁'-path : ∀ x → h₁' x == ! (ap [_]₂ (η (EM₁-antipodal-map (cp₀₁ h x))))
        h₁'-path x =
          transport (λ y → ∀ x → antipodal-map (cp₁₁ y x) == [ north ]₂) (emloop h) h₀' x
            =⟨ app= (Π-transp (emloop h) h₀') x ⟩
          transport (λ y → antipodal-map (cp₁₁ y x) == [ north ]₂) (emloop h) (h₀' x)
            =⟨ to-transp {B = λ y → antipodal-map (cp₁₁ y x) == [ north ]₂} {p = emloop h} $
               ↓-app=cst-in' {f = λ y → antipodal-map (cp₁₁ y x)} {p = emloop h} {u = idp} {v = ! (ap (λ y → antipodal-map (cp₁₁ y x)) (emloop h))} $
               ! (!-inv-r (ap (λ y → antipodal-map (cp₁₁ y x)) (emloop h))) ∙
               ∙=∙' (ap (λ y → antipodal-map (cp₁₁ y x)) (emloop h)) (! (ap (λ y → antipodal-map (cp₁₁ y x)) (emloop h))) ⟩
          ! (ap (λ y → antipodal-map (cp₁₁ y x)) (emloop h))
            =⟨ ap ! (ap-∘ antipodal-map (λ y → cp₁₁ y x) (emloop h)) ⟩
          ! (ap antipodal-map (ap (λ y → cp₁₁ y x) (emloop h)))
            =⟨ ap (! ∘ ap antipodal-map) (ap-cp₁₁ h x) ⟩
          ! (ap antipodal-map (ap [_]₂ (η (cp₀₁ h x))))
            =⟨ ap ! (∘-ap antipodal-map [_]₂ (η (cp₀₁ h x))) ⟩
          ! (ap (λ p → [ Susp-fmap EM₁-antipodal-map p ]₂) (η (cp₀₁ h x)))
            =⟨ ap ! (ap-∘ [_]₂ (Susp-fmap EM₁-antipodal-map) (η (cp₀₁ h x))) ⟩
          ! (ap [_]₂ (ap (Susp-fmap EM₁-antipodal-map) (η (cp₀₁ h x))))
            =⟨ ! (ap (! ∘ ap [_]₂) (app= (ap fst (η-natural ⊙EM₁-antipodal-map)) (cp₀₁ h x))) ⟩
          ! (ap [_]₂ (η (EM₁-antipodal-map (cp₀₁ h x)))) =∎
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
            =ₛ⟨ =ₛ-in {t = ! (!-inv-r (! (ap [_]₂ (η embase)))) ◃∙
                            ap (λ v → ! (ap [_]₂ (η (cp₀₁ g v))) ∙ ! (! (ap [_] (η embase)))) (emloop h) ◃∙
                            !-inv-r (! (ap [_]₂ (η embase))) ◃∎} $
                ap (λ f → ! (!-inv-r (f embase)) ∙
                          ap (λ v → f v ∙ ! (f embase)) (emloop h) ∙
                          !-inv-r (f embase))
                    (λ= h₁-path) ⟩
          ! (!-inv-r (! (ap [_]₂ (η embase)))) ◃∙
          ap (λ v → ! (ap [_]₂ (η (cp₀₁ g v))) ∙ ! (! (ap [_]₂ (η embase)))) (emloop h) ◃∙
          !-inv-r (! (ap [_]₂ (η embase))) ◃∎
            =ₛ₁⟨ 1 & 1 &
                  ap (λ v → ! (ap [_]₂ (η (cp₀₁ g v))) ∙ ! (! (ap [_]₂ (η embase)))) (emloop h)
                    =⟨ ap-∘ (λ w → ! (ap [_]₂ (η w)) ∙ ! (! (ap [_]₂ (η embase)))) (cp₀₁ g) (emloop h) ⟩
                  ap (λ w → ! (ap [_]₂ (η w)) ∙ ! (! (ap [_]₂ (η embase)))) (ap (cp₀₁ g) (emloop h))
                    =⟨ ap (ap (λ w → ! (ap [_]₂ (η w)) ∙ ! (! (ap [_]₂ (η embase))))) $
                      ap (cp₀₁ g) (emloop h)
                        =⟨ CP₀₁-comm.cp₀₁-comm g h ⟩
                      ap (cp₀₁ h) (emloop g)
                        =⟨ cp₀₁-emloop-β h g ⟩
                      emloop (R.mult h g)
                        =⟨ ! (!-! (emloop (R.mult h g))) ⟩
                      ! (! (emloop (R.mult h g)))
                        =⟨ ap ! (! (EM₁-antipodal-map-! (R.mult h g))) ⟩
                      ! (ap EM₁-antipodal-map (emloop (R.mult h g)))
                        =⟨ ap (! ∘ ap EM₁-antipodal-map) (! (cp₀₁-emloop-β h g)) ⟩
                      ! (ap EM₁-antipodal-map (ap (cp₀₁ h) (emloop g)))
                        =⟨ ap ! (∘-ap EM₁-antipodal-map (cp₀₁ h) (emloop g)) ⟩
                      ! (ap (EM₁-antipodal-map ∘ cp₀₁ h) (emloop g)) =∎
                      -- Yo dawg, I herd you like continued equalities,
                      -- so we put continued equalities into your continued equalities,
                      -- so you can reason equationally while u reason equationally.
                    ⟩
                  ap (λ w → ! (ap [_]₂ (η w)) ∙ ! (! (ap [_]₂ (η embase)))) (! (ap (EM₁-antipodal-map ∘ cp₀₁ h) (emloop g)))
                    =⟨ ap-! (λ w → ! (ap [_]₂ (η w)) ∙ ! (! (ap [_]₂ (η embase)))) (ap (EM₁-antipodal-map ∘ cp₀₁ h) (emloop g)) ⟩
                  ! (ap (λ w → ! (ap [_]₂ (η w)) ∙ ! (! (ap [_]₂ (η embase)))) (ap (EM₁-antipodal-map ∘ cp₀₁ h) (emloop g)))
                    =⟨ ap ! (∘-ap (λ w → ! (ap [_]₂ (η w)) ∙ ! (! (ap [_]₂ (η embase)))) (EM₁-antipodal-map ∘ cp₀₁ h) (emloop g)) ⟩
                  ! (ap (λ v → ! (ap [_]₂ (η (EM₁-antipodal-map (cp₀₁ h v)))) ∙ ! (! (ap [_]₂ (η embase)))) (emloop g)) =∎
                ⟩
          ! (!-inv-r (! (ap [_]₂ (η embase)))) ◃∙
          ! (ap (λ v → ! (ap [_]₂ (η (EM₁-antipodal-map (cp₀₁ h v)))) ∙ ! (! (ap [_]₂ (η embase)))) (emloop g)) ◃∙
          !-inv-r (! (ap [_]₂ (η embase))) ◃∎
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
          ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h) ◃∙
          ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (ap-cst [ north ] (emloop h)) ◃∙
          ap (idp ∙_) (ap-cp₁₁-embase g) ◃∎
           =ₛ
          ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_)
             (homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h)) ◃∙
          ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
          ap (_∙ idp) (ap-cp₁₁-embase g) ◃∎
        top-part =
          ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h) ◃∙
          ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (ap-cst [ north ] (emloop h)) ◃∙
          ap (idp ∙_) (ap-cp₁₁-embase g) ◃∎
            =ₛ₁⟨ 1 & 1 & ap (ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)))
                            (! (homotopy-naturality-cst-to-cst {A = EM₁ R₊} {B = EM 2} [ north ]₂ (emloop' R₊ h))) ⟩
          ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h) ◃∙
          ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g))
             (homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ (λ y → idp) (emloop' R₊ h)) ◃∙
          ap (idp ∙_) (ap-cp₁₁-embase g) ◃∎
            =ₛ⟨ 0 & 2 & post-rotate-out {r = _ ◃∙ _ ◃∙ _ ◃∎} $
                        ap-comm-cst-coh cp₁₁ (emloop g) (emloop h) [ north ]₂ (λ y → idp) ⟩
          ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_)
              (homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h)) ◃∙
          ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_)
             (app= (transp-naturality {B = λ x → ∀ y → cp₁₁ x y == [ north ]₂} {C = λ x → cp₁₁ x embase == cp₁₁ x embase}
                                      (λ h → h embase ∙ ! (h embase)) (emloop g))
                   (λ y → idp)) ◃∙
          ! (ap-transp (λ x → cp₁₁ x embase) (λ x → cp₁₁ x embase) (emloop g) idp) ◃∙
          ap (idp ∙_) (ap-cp₁₁-embase g) ◃∎
            =ₛ⟨ 1 & 1 & ap-seq-=ₛ (ap (λ x → cp₁₁ x embase) (emloop g) ∙_)
                                  (transp-nat-idp cp₁₁ (emloop g) embase [ north ]₂ (λ y → idp)) ⟩
          ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_)
             (homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h)) ◃∙
          ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
          ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_)
             (! (transp-idp (λ a → cp₁₁ a embase) (emloop g))) ◃∙
          idp ◃∙
          ! (ap-transp (λ x → cp₁₁ x embase) (λ x → cp₁₁ x embase) (emloop g) idp) ◃∙
          ap (idp ∙_) (ap-cp₁₁-embase g) ◃∎
            =ₛ⟨ 3 & 1 & expand [] ⟩
          ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_)
             (homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h)) ◃∙
          ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
          ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_)
             (! (transp-idp (λ a → cp₁₁ a embase) (emloop g))) ◃∙
          ! (ap-transp (λ x → cp₁₁ x embase) (λ x → cp₁₁ x embase) (emloop g) idp) ◃∙
          ap (idp ∙_) (ap-cp₁₁-embase g) ◃∎
            =ₛ₁⟨ 2 & 1 & ap-! (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (transp-idp (λ a → cp₁₁ a embase) (emloop g)) ⟩
          ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_)
             (homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h)) ◃∙
          ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
          ! (ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_)
                (transp-idp (λ a → cp₁₁ a embase) (emloop g))) ◃∙
          ! (ap-transp (λ x → cp₁₁ x embase) (λ x → cp₁₁ x embase) (emloop g) idp) ◃∙
          ap (idp ∙_) (ap-cp₁₁-embase g) ◃∎
            =ₛ⟨ 2 & 2 & pre-rotate'-seq-in {p = _ ◃∙ _ ◃∎} {r = []} $
                        !ₛ $ ap-transp-idp (λ x → cp₁₁ x embase) (emloop g) ⟩
          ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_)
             (homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h)) ◃∙
          ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
          ∙-unit-r (ap (λ x → cp₁₁ x embase) (emloop g)) ◃∙
          ap (idp ∙_) (ap-cp₁₁-embase g) ◃∎
            =ₛ⟨ 2 & 2 & !ₛ $ homotopy-naturality (_∙ idp) (idp ∙_) ∙-unit-r (ap-cp₁₁-embase g) ⟩
          ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_)
             (homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h)) ◃∙
          ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
          ap (_∙ idp) (ap-cp₁₁-embase g) ◃∙
          idp ◃∎
            =ₛ⟨ 3 & 1 & expand [] ⟩
          ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_)
              (homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h)) ◃∙
          ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
          ap (_∙ idp) (ap-cp₁₁-embase g) ◃∎ ∎ₛ
        bottom-part :
          ap (_∙ idp) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
          ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (! (!-inv-r (h₁' embase))) ◃∙
          ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_)
             (! (homotopy-naturality-to-cst (λ x → [ north ]₂) [ north ]₂ h₁' (emloop g))) ◃∎
          =ₛ
          ap (idp ∙_) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
          ap (_∙ ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h)) (! (ap-cst [ north ]₂ (emloop g))) ◃∙
          ap-comm (λ x y → antipodal-map (cp₁₁ y x)) (emloop g) (emloop h) ◃∎
        bottom-part =
          ap (λ a → a ∙ idp) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
          ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (! (!-inv-r (h₁' embase))) ◃∙
          ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_)
             (! (homotopy-naturality-to-cst (λ x → [ north ]₂) [ north ]₂ h₁' (emloop g))) ◃∎
            =ₛ⟨ 0 & 0 & contract ⟩
          idp ◃∙
          ap (_∙ idp) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
          ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (! (!-inv-r (h₁' embase))) ◃∙
          ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_)
             (! (homotopy-naturality-to-cst (λ x → [ north ]₂) [ north ]₂ h₁' (emloop g))) ◃∎
            =ₛ⟨ 0 & 2 & !ₛ (homotopy-naturality (idp ∙_) (_∙ idp) (! ∘ ∙-unit-r) (↯ (tail (comm-embase-emloop↯ h)))) ⟩
          ap (idp ∙_) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
          ! (∙-unit-r (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h))) ◃∙
          ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (! (!-inv-r (h₁' embase))) ◃∙
          ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_)
             (! (homotopy-naturality-to-cst (λ x → [ north ]₂) [ north ]₂ h₁' (emloop g))) ◃∎
            =ₛ⟨ 1 & 1 & !ₛ $ post-rotate-in {p = _ ◃∙ _ ◃∎} $
                        ap-transp-idp (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ⟩
          ap (idp ∙_) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
          ap-transp (λ y → antipodal-map (cp₁₁ y embase)) (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) idp ◃∙
          ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (transp-idp (λ y → antipodal-map (cp₁₁ y embase)) (emloop h)) ◃∙
          ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (! (!-inv-r (h₁' embase))) ◃∙
          ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_)
             (! (homotopy-naturality-to-cst (λ x → [ north ]₂) [ north ]₂ h₁' (emloop g))) ◃∎
            =ₛ⟨ 2 & 2 & ap-seq-=ₛ (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) $
                transp-idp (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ◃∙
                ! (!-inv-r (h₁' embase)) ◃∎
                  =ₛ⟨ pre-rotate-out $ pre-rotate'-in $ post-rotate-in {p = []} $
                      transp-nat-idp (λ y x → antipodal-map (cp₁₁ y x)) (emloop h) embase [ north ]₂ (λ x → idp) ⟩
                idp ◃∙
                ! (app= (transp-naturality {B = λ y → ∀ x → antipodal-map (cp₁₁ y x) == [ north ]₂}
                                           (λ h → h embase ∙ ! (h embase)) (emloop h))
                        (λ x → idp)) ◃∎
                  =ₛ⟨ 0 & 1 & expand [] ⟩
                ! (app= (transp-naturality {B = λ y → ∀ x → antipodal-map (cp₁₁ y x) == [ north ]₂}
                                           (λ h → h embase ∙ ! (h embase)) (emloop h))
                        (λ x → idp)) ◃∎ ∎ₛ
              ⟩
          ap (idp ∙_) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
          ap-transp (λ y → antipodal-map (cp₁₁ y embase)) (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) idp ◃∙
          ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_)
             (! (app= (transp-naturality {B = λ y → ∀ x → antipodal-map (cp₁₁ y x) == [ north ]₂}
                                         (λ h → h embase ∙ ! (h embase)) (emloop h))
                      (λ x → idp))) ◃∙
          ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_)
             (! (homotopy-naturality-to-cst (λ x → [ north ]₂) [ north ]₂ h₁' (emloop g))) ◃∎
            =ₛ₁⟨ 2 & 1 & ap-! (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_)
                              (app= (transp-naturality {B = λ y → ∀ x → antipodal-map (cp₁₁ y x) == [ north ]₂}
                                                       (λ h → h embase ∙ ! (h embase)) (emloop h))
                                    (λ x → idp)) ⟩
          ap (idp ∙_) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
          ap-transp (λ y → antipodal-map (cp₁₁ y embase)) (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) idp ◃∙
          ! (ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_)
                (app= (transp-naturality {B = λ y → ∀ x → antipodal-map (cp₁₁ y x) == [ north ]₂}
                                         (λ h → h embase ∙ ! (h embase)) (emloop h))
                      (λ x → idp))) ◃∙
          ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_)
             (! (homotopy-naturality-to-cst (λ x → [ north ]₂) [ north ]₂ h₁' (emloop g))) ◃∎
            =ₛ₁⟨ 3 & 1 & ap-! (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_)
                              (homotopy-naturality-to-cst (λ x → [ north ]₂) [ north ]₂ h₁' (emloop g)) ⟩
          ap (idp ∙_) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
          ap-transp (λ y → antipodal-map (cp₁₁ y embase)) (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) idp ◃∙
          ! (ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_)
                (app= (transp-naturality {B = λ y → ∀ x → antipodal-map (cp₁₁ y x) == [ north ]₂}
                                         (λ h → h embase ∙ ! (h embase)) (emloop h))
                      (λ x → idp))) ◃∙
          ! (ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_)
                (homotopy-naturality-to-cst (λ x → [ north ]₂) [ north ]₂ h₁' (emloop g))) ◃∎
            =ₛ⟨ 1 & 3 & pre-rotate-out $
                        pre-rotate'-seq-in {p = _ ◃∙ _ ◃∎} $
                        post-rotate-in {p = []} $
                        ap-comm-cst-coh (λ y x → antipodal-map (cp₁₁ y x))
                                        (emloop h) (emloop g) [ north ]₂ (λ x → idp) ⟩
          ap (idp ∙_) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
          ! (ap (_∙ ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h))
                (homotopy-naturality-to-cst (λ x → antipodal-map (cp₁₁ embase x))
                                            [ north ]₂ (λ x → idp) (emloop g))) ◃∙
          ! (ap-comm (λ y x → antipodal-map (cp₁₁ y x)) (emloop h) (emloop g)) ◃∎
            =ₛ₁⟨ 2 & 1 & ! (ap-comm-comm (λ x y → antipodal-map (cp₁₁ y x)) (emloop g) (emloop h)) ⟩
          ap (idp ∙_) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
          ! (ap (_∙ ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h))
                (homotopy-naturality-to-cst (λ x → antipodal-map (cp₁₁ embase x))
                                            [ north ]₂ (λ x → idp) (emloop g))) ◃∙
          ap-comm (λ x y → antipodal-map (cp₁₁ y x)) (emloop g) (emloop h) ◃∎
            =ₛ₁⟨ 1 & 1 &
                 ! (ap (_∙ ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h))
                       (homotopy-naturality-to-cst (λ x → antipodal-map (cp₁₁ embase x))
                                                   [ north ]₂ (λ x → idp) (emloop g)))
                   =⟨ !-ap (_∙ ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h))
                           (homotopy-naturality-to-cst (λ x → antipodal-map (cp₁₁ embase x))
                                                       [ north ]₂ (λ x → idp) (emloop g)) ⟩
                 ap (_∙ ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h))
                    (! (homotopy-naturality-to-cst (λ x → antipodal-map (cp₁₁ embase x))
                                                   [ north ]₂ (λ x → idp) (emloop g)))
                   =⟨ ap (ap (_∙ ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h)) ∘ !) $
                      homotopy-naturality-cst-to-cst [ north ]₂ (emloop g) ⟩
                 ap (_∙ ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h)) (! (ap-cst [ north ]₂ (emloop g))) =∎
               ⟩
          ap (idp ∙_) (↯ (tail (comm-embase-emloop↯ h))) ◃∙
          ap (_∙ ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h)) (! (ap-cst [ north ]₂ (emloop g))) ◃∙
          ap-comm (λ x y → antipodal-map (cp₁₁ y x)) (emloop g) (emloop h) ◃∎ ∎ₛ
        step₄' : ! (ap-cst [ north ] (emloop g)) ◃∎
                 =ₛ
                 ↯ h₁'-seq ◃∙
                 ! (!-inv-r (h₁' embase)) ◃∙
                 ! (homotopy-naturality-to-cst (λ x → [ north ]₂) [ north ]₂ h₁' (emloop g)) ◃∎
        step₄' = pre-rotate'-in $ post-rotate-seq-in {p = []} $ !ₛ $
          ap-cst [ north ]₂ (emloop g) ◃∙
          ↯ h₁'-seq ◃∎
            =ₛ⟨ 1 & 1 & expand h₁'-seq ⟩
          ap-cst [ north ] (emloop g) ◃∙
          ! (!-inv-r (h₁' embase)) ◃∙
          ! (ap (λ v → h₁' v ∙ ! (h₁' embase)) (emloop g)) ◃∙
          !-inv-r (h₁' embase) ◃∎
            =ₛ⟨ 0 & 2 & !ₛ $ post-rotate-in {p = _ ◃∙ _ ◃∎} $
                        homotopy-naturality-cst-to-cst' [ north ]₂ [ north ]₂ h₁' (emloop g) ⟩
          homotopy-naturality-to-cst (cst [ north ]₂) [ north ]₂ h₁' (emloop g) ◃∙
          ap (λ v → h₁' v ∙ ! (h₁' embase)) (emloop g) ◃∙
          ! (ap (λ v → h₁' v ∙ ! (h₁' embase)) (emloop g)) ◃∙
          !-inv-r (h₁' embase) ◃∎
            =ₛ⟨ 1 & 2 & seq-!-inv-r (ap (λ v → h₁' v ∙ ! (h₁' embase)) (emloop g) ◃∎) ⟩
          homotopy-naturality-to-cst (cst [ north ]₂) [ north ]₂ h₁' (emloop g) ◃∙
          !-inv-r (h₁' embase) ◃∎ ∎ₛ
        step₁₃' :
          homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h) ◃∙
          !-inv-r (h₁ embase) ◃∙
          ↯ h₁-seq ◃∎
          =ₛ
          ap-cst [ north ]₂ (emloop h) ◃∎
        step₁₃' =
          homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h) ◃∙
          !-inv-r (h₁ embase) ◃∙
          ↯ h₁-seq ◃∎
            =ₛ⟨ 2 & 1 & expand h₁-seq ⟩
          homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h) ◃∙
          !-inv-r (h₁ embase) ◃∙
          ! (!-inv-r (h₁ embase)) ◃∙
          ap (λ v → h₁ v ∙ ! (h₁ embase)) (emloop h) ◃∙
          !-inv-r (h₁ embase) ◃∎
            =ₛ⟨ 1 & 2 & seq-!-inv-r (!-inv-r (h₁ embase) ◃∎) ⟩
          homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h) ◃∙
          ap (λ v → h₁ v ∙ ! (h₁ embase)) (emloop h) ◃∙
          !-inv-r (h₁ embase) ◃∎
            =ₛ⟨ homotopy-naturality-cst-to-cst' [ north ]₂ [ north ]₂ h₁ (emloop h) ⟩
          ap-cst [ north ]₂ (emloop h) ◃∎ ∎ₛ

    abstract

      comm-embase-emloop : ∀ h →
        Square idp
               (ap (cp₁₁ embase) (emloop h))
               (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h))
               idp
      comm-embase-emloop h = vert-degen-square (comm-embase-emloop' h)

      comm-emloop-embase : ∀ g →
        Square idp
               (ap (λ x → cp₁₁ x embase) (emloop g))
               (ap (λ x → antipodal-map (cp₁₁ embase x)) (emloop g))
               idp
      comm-emloop-embase g = vert-degen-square (comm-emloop-embase' g)

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
        comm-embase-emloop (R.add h₁ h₂) ⊡v∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase))) (emloop-comp h₁ h₂)
        ==
        ap (ap (λ y → cp₁₁ embase y)) (emloop-comp h₁ h₂) ∙v⊡
        ↓-='-square-comp (comm-embase-emloop h₁) (comm-embase-emloop h₂)
      comm-embase-emloop-comp h₁ h₂ =
        comm-embase-emloop (R.add h₁ h₂) ⊡v∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase))) (emloop-comp h₁ h₂)
          =⟨ vert-degen-square-⊡v∙
               (comm-embase-emloop' (R.add h₁ h₂))
               (ap (ap (λ y → antipodal-map (cp₁₁ y embase))) (emloop-comp h₁ h₂)) ⟩
        vert-degen-square
          (comm-embase-emloop' (R.add h₁ h₂) ∙
           ap (ap (λ y → antipodal-map (cp₁₁ y embase))) (emloop-comp h₁ h₂))
          =⟨ ap vert-degen-square (=ₛ-out (comm-embase-emloop-comp' h₁ h₂)) ⟩
        vert-degen-square
          (ap (ap (λ y → cp₁₁ embase y)) (emloop-comp h₁ h₂) ∙
           ap-∙ (λ y → cp₁₁ embase y) (emloop h₁) (emloop h₂) ∙
           ap2 _∙_ (comm-embase-emloop' h₁) (comm-embase-emloop' h₂) ∙
           ∙-ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h₁) (emloop h₂))
          =⟨ ! $ vert-degen-square-∙v⊡ (ap (ap (λ y → cp₁₁ embase y)) (emloop-comp h₁ h₂)) _ ⟩
        ap (ap (λ y → cp₁₁ embase y)) (emloop-comp h₁ h₂) ∙v⊡
        vert-degen-square
          (ap-∙ (λ y → cp₁₁ embase y) (emloop h₁) (emloop h₂) ∙
           ap2 _∙_ (comm-embase-emloop' h₁) (comm-embase-emloop' h₂) ∙
           ∙-ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h₁) (emloop h₂))
          =⟨ ap (ap (ap (λ y → cp₁₁ embase y)) (emloop-comp h₁ h₂) ∙v⊡_) $ ! $
             square-helper
               (ap-∙ (λ y → cp₁₁ embase y) (emloop h₁) (emloop h₂))
               (comm-embase-emloop' h₁) (comm-embase-emloop' h₂)
               (∙-ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h₁) (emloop h₂)) ⟩
        ap (ap (λ y → cp₁₁ embase y)) (emloop-comp h₁ h₂) ∙v⊡
        ↓-='-square-comp' (comm-embase-emloop h₁) (comm-embase-emloop h₂)
          =⟨ ap (ap (ap (λ y → cp₁₁ embase y)) (emloop-comp h₁ h₂) ∙v⊡_) $
             ↓-='-square-comp'=↓-='-square-comp
               (comm-embase-emloop h₁) (comm-embase-emloop h₂) ⟩
        ap (ap (λ y → cp₁₁ embase y)) (emloop-comp h₁ h₂) ∙v⊡
        ↓-='-square-comp (comm-embase-emloop h₁) (comm-embase-emloop h₂) =∎

      comm-emloop-comp-embase : ∀ g₁ g₂ →
        comm-emloop-embase (R.add g₁ g₂) ⊡v∙
        ap (ap (λ x → antipodal-map (cp₁₁ embase x))) (emloop-comp g₁ g₂)
        ==
        ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ∙v⊡
        ↓-='-square-comp (comm-emloop-embase g₁) (comm-emloop-embase g₂)
      comm-emloop-comp-embase g₁ g₂ =
        comm-emloop-embase (R.add g₁ g₂) ⊡v∙
        ap (ap (λ x → antipodal-map (cp₁₁ embase x))) (emloop-comp g₁ g₂)
          =⟨ vert-degen-square-⊡v∙
               (comm-emloop-embase' (R.add g₁ g₂))
               (ap (ap (λ x → antipodal-map (cp₁₁ embase x))) (emloop-comp g₁ g₂)) ⟩
        vert-degen-square
          (comm-emloop-embase' (R.add g₁ g₂) ∙
           ap (ap (λ x → antipodal-map (cp₁₁ embase x))) (emloop-comp g₁ g₂))
           =⟨ ap vert-degen-square (=ₛ-out (comm-emloop-comp-embase' g₁ g₂)) ⟩
        vert-degen-square
          (ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ∙
           ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂) ∙
           ap2 _∙_ (comm-emloop-embase' g₁) (comm-emloop-embase' g₂) ∙
           ∙-ap (λ x → antipodal-map (cp₁₁ embase x)) (emloop g₁) (emloop g₂))
          =⟨ ! $ vert-degen-square-∙v⊡ (ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂)) _ ⟩
        ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ∙v⊡
        vert-degen-square
          (ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂) ∙
           ap2 _∙_ (comm-emloop-embase' g₁) (comm-emloop-embase' g₂) ∙
           ∙-ap (λ x → antipodal-map (cp₁₁ embase x)) (emloop g₁) (emloop g₂))
          =⟨ ap (ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ∙v⊡_) $ ! $
             square-helper
               (ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂))
               (comm-emloop-embase' g₁) (comm-emloop-embase' g₂)
               (∙-ap (λ x → antipodal-map (cp₁₁ embase x)) (emloop g₁) (emloop g₂)) ⟩
        ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ∙v⊡
        ↓-='-square-comp' (comm-emloop-embase g₁) (comm-emloop-embase g₂)
          =⟨ ap (ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ∙v⊡_) $
             ↓-='-square-comp'=↓-='-square-comp
               (comm-emloop-embase g₁) (comm-emloop-embase g₂) ⟩
        ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ∙v⊡
        ↓-='-square-comp (comm-emloop-embase g₁) (comm-emloop-embase g₂) =∎

      comm-emloop-emloop : ∀ g h →
        ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h) ∙v⊡
        comm-embase-emloop h ⊡h comm-emloop-embase g
        ==
        (comm-emloop-embase g ⊡h comm-embase-emloop h) ⊡v∙
        ap-comm (λ x y → antipodal-map (cp₁₁ y x)) (emloop g) (emloop h)
      comm-emloop-emloop g h =
        ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h) ∙v⊡
        comm-embase-emloop h ⊡h comm-emloop-embase g
          =⟨ ap (ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h) ∙v⊡_) $
             vert-degen-square-⊡h (comm-embase-emloop' h) (comm-emloop-embase' g) ⟩
        ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h) ∙v⊡
        vert-degen-square (ap2 _∙_ (comm-embase-emloop' h) (comm-emloop-embase' g))
          =⟨ vert-degen-square-∙v⊡ (ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h)) _ ⟩
        vert-degen-square
          (ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h) ∙
           ap2 _∙_ (comm-embase-emloop' h) (comm-emloop-embase' g))
          =⟨ ap vert-degen-square (=ₛ-out (comm-emloop-emloop' g h)) ⟩
        vert-degen-square
          (ap2 _∙_ (comm-emloop-embase' g) (comm-embase-emloop' h) ∙
           ap-comm (λ x y → antipodal-map (cp₁₁ y x)) (emloop g) (emloop h))
          =⟨ ! $ vert-degen-square-⊡v∙ _ (ap-comm (λ x y → antipodal-map (cp₁₁ y x)) (emloop g) (emloop h)) ⟩
        vert-degen-square (ap2 _∙_ (comm-emloop-embase' g) (comm-embase-emloop' h)) ⊡v∙
        ap-comm (λ x y → antipodal-map (cp₁₁ y x)) (emloop g) (emloop h)
          =⟨ ap (_⊡v∙ ap-comm (λ x y → antipodal-map (cp₁₁ y x)) (emloop g) (emloop h)) $ ! $
             vert-degen-square-⊡h (comm-emloop-embase' g) (comm-embase-emloop' h) ⟩
        (comm-emloop-embase g ⊡h comm-embase-emloop h) ⊡v∙
        ap-comm (λ x y → antipodal-map (cp₁₁ y x)) (emloop g) (emloop h) =∎

    private
      module CP₁₁Comm =
        EM₁Level₂DoublePathElim R₊ R₊ {C = EM 2} {{Trunc-level}}
          (λ x y → cp₁₁ x y)
          (λ x y → antipodal-map (cp₁₁ y x))
          idp
          comm-embase-emloop
          comm-emloop-embase
          comm-embase-emloop-comp
          comm-emloop-comp-embase
          comm-emloop-emloop

    abstract
      cp₁₁-comm : ∀ x y → cp₁₁ x y == antipodal-map (cp₁₁ y x)
      cp₁₁-comm = CP₁₁Comm.f
