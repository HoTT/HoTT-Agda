{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane
open import cohomology.CupProduct.OnEM.EM1DoubleElim

module cohomology.CupProduct.OnEM.Commutativity {i} (R : CRing i) where

  open import cohomology.CupProduct.OnEM.Definition R
  open CP₁₁

  open EMExplicit R.add-ab-group

  EM₁-antipodal-map : EM₁ R₊ → EM₁ R₊
  EM₁-antipodal-map = EM₁-fmap (inv-hom R.add-ab-group)

  ⊙EM₁-antipodal-map : ⊙EM₁ R₊ ⊙→ ⊙EM₁ R₊
  ⊙EM₁-antipodal-map = EM₁-antipodal-map , idp

  antipodal-map : EM 2 → EM 2
  antipodal-map = Trunc-fmap (Susp-fmap EM₁-antipodal-map)

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
          =ₛ⟨ 1 & 1 & ap-seq-∙ (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (comm-embase-emloop↯ h) ⟩
        ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (ap-cst [ north ] (emloop h)) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (! (ap (ap antipodal-map) (ap-cp₁₁-embase h))) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop h)) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (comm-emloop-embase' g) ◃∎
          =ₛ₁⟨ 1 & 1 & ap (ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)))
                          (! (homotopy-naturality-cst-to-cst {A = EM₁ R₊} {B = EM 2} [ north ]₂ (emloop' R₊ h))) ⟩
        ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ (λ y → idp) (emloop' R₊ h)) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (! (ap (ap antipodal-map) (ap-cp₁₁-embase h))) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop h)) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (comm-emloop-embase' g) ◃∎
          =ₛ⟨ 0 & 2 & post-rotate-out {r = _ ◃∙ _ ◃∙ _ ◃∎} $
                      ap-comm-cst-coh cp₁₁ (emloop g) (emloop h) [ north ]₂ (λ y → idp) ⟩
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_)
            (homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h)) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_)
           (ap (λ k → k (λ y → idp))
               (transp-naturality {B = λ x → ∀ y → cp₁₁ x y == [ north ]₂} {C = λ x → cp₁₁ x embase == cp₁₁ x embase}
                                  (λ h → h embase ∙ ! (h embase)) (emloop g))) ◃∙
        ! (ap-transp (λ x → cp₁₁ x embase) (λ x → cp₁₁ x embase) (emloop g) idp) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (! (ap (ap antipodal-map) (ap-cp₁₁-embase h))) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop h)) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (comm-emloop-embase' g) ◃∎
          =ₛ⟨ 0 & 2 & ap-seq-=ₛ (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) step₅' ⟩
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (ap-cst [ north ]₂ (emloop h)) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (! (!-inv-r (h₁ embase))) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (! (ap (λ v → h₁ v ∙ ! (h₁ embase)) (emloop h))) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (! (transp-idp (λ a → cp₁₁ a embase) (emloop g))) ◃∙
        ! (ap-transp (λ x → cp₁₁ x embase) (λ x → cp₁₁ x embase) (emloop g) idp) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (! (ap (ap antipodal-map) (ap-cp₁₁-embase h))) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop h)) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (comm-emloop-embase' g) ◃∎
          =ₛ₁⟨ 4 & 1 & ap-! (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (transp-idp (λ a → cp₁₁ a embase) (emloop g)) ⟩
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (ap-cst [ north ]₂ (emloop h)) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (! (!-inv-r (h₁ embase))) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (! (ap (λ v → h₁ v ∙ ! (h₁ embase)) (emloop h))) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
        ! (ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (transp-idp (λ a → cp₁₁ a embase) (emloop g))) ◃∙
        ! (ap-transp (λ x → cp₁₁ x embase) (λ x → cp₁₁ x embase) (emloop g) idp) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (! (ap (ap antipodal-map) (ap-cp₁₁-embase h))) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop h)) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (comm-emloop-embase' g) ◃∎
          =ₛ⟨ 4 & 2 & pre-rotate'-seq-in {p = _ ◃∙ _ ◃∎} {r = []} $
                      !ₛ $ ap-transp-idp (λ x → cp₁₁ x embase) (emloop g) ⟩
        {!ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (ap-cst [ north ]₂ (emloop h)) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (! (!-inv-r (h₁ embase))) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (! (ap (λ v → h₁ v ∙ ! (h₁ embase)) (emloop h))) ◃∙
        ap (ap (λ x → cp₁₁ x embase) (emloop g) ∙_) (!-inv-r (h₁ embase)) ◃∙
        ∙-unit-r (ap (λ x → cp₁₁ x embase) (emloop g)) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (! (ap (ap antipodal-map) (ap-cp₁₁-embase h))) ◃∙
        ap (_∙ ap (λ x → cp₁₁ x embase) (emloop g)) (∘-ap antipodal-map (λ y → cp₁₁ y embase) (emloop h)) ◃∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) ∙_) (comm-emloop-embase' g) ◃∎
          =ₛ⟨ ? ⟩
        ?!}
        where
          h₀ : ∀ y → cp₁₁ embase y == [ north ]₂
          h₀ y = idp
          h₁ : ∀ y → cp₁₁ embase y == [ north ]₂
          h₁ = transport (λ x → ∀ y → cp₁₁ x y == [ north ]₂) (emloop g) h₀
          h₀' : ∀ x → antipodal-map (cp₁₁ embase x) == [ north ]₂
          h₀' x = idp
          h₁' : ∀ x → antipodal-map (cp₁₁ embase x) == [ north ]₂
          h₁' = transport (λ y → ∀ x → antipodal-map (cp₁₁ y x) == [ north ]₂) (emloop h) h₀'
          h₁-path : ∀ y → h₁ y == ! (ap [_] (η (cp₀₁ g y)))
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
          {- the crucial step in the commutative diagram -}
          heart : ! (!-inv-r (h₁ embase)) ◃∙
                  ap (λ v → h₁ v ∙ ! (h₁ embase)) (emloop h) ◃∙
                  !-inv-r (h₁ embase) ◃∎
                  =ₛ
                  ! (!-inv-r (h₁' embase)) ◃∙
                  ap (λ v → h₁' v ∙ ! (h₁' embase)) (emloop g) ◃∙
                  !-inv-r (h₁' embase) ◃∎
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
                     =⟨ ap (ap (λ w → ! (ap [_]₂ (η w)) ∙ ! (! (ap [_]₂ (η embase))))) {!!} ⟩
                   ap (λ w → ! (ap [_]₂ (η w)) ∙ ! (! (ap [_]₂ (η embase)))) (ap (EM₁-antipodal-map ∘ cp₀₁ h) (emloop g))
                     =⟨ ∘-ap (λ w → ! (ap [_]₂ (η w)) ∙ ! (! (ap [_]₂ (η embase)))) (EM₁-antipodal-map ∘ cp₀₁ h) (emloop g) ⟩
                   ap (λ v → ! (ap [_]₂ (η (EM₁-antipodal-map (cp₀₁ h v)))) ∙ ! (! (ap [_]₂ (η embase)))) (emloop g) =∎
                 ⟩
            ! (!-inv-r (! (ap [_]₂ (η embase)))) ◃∙
            ap (λ v → ! (ap [_]₂ (η (EM₁-antipodal-map (cp₀₁ h v)))) ∙ ! (! (ap [_]₂ (η embase)))) (emloop g) ◃∙
            !-inv-r (! (ap [_]₂ (η embase))) ◃∎
              =ₛ⟨ =ₛ-in {t = ! (!-inv-r (h₁' embase)) ◃∙
                             ap (λ v → h₁' v ∙ ! (h₁' embase)) (emloop g) ◃∙
                             !-inv-r (h₁' embase) ◃∎} $
                  ap (λ f → ! (!-inv-r (f embase)) ∙
                            ap (λ v → f v ∙ ! (f embase)) (emloop g) ∙
                            !-inv-r (f embase))
                     (! (λ= h₁'-path)) ⟩
            ! (!-inv-r (h₁' embase)) ◃∙
            ap (λ v → h₁' v ∙ ! (h₁' embase)) (emloop g) ◃∙
            !-inv-r (h₁' embase) ◃∎ ∎ₛ
          foo : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A → B → C)
            {a₀ a₁ : A} (p : a₀ == a₁) (b : B)
            (c : C) (h₀ : ∀ b' → f a₀ b' == c)
            → ap (λ k → k h₀) (transp-naturality {B = λ a → ∀ b → f a b == c} (λ h → h b ∙ ! (h b)) p) ◃∎
              =ₛ
              !-inv-r (transport (λ a → ∀ b → f a b == c) p h₀ b) ◃∙
              ! (transp-idp (λ a → f a b) p) ◃∙
              ap (transport (λ a → f a b == f a b) p) (! (!-inv-r (h₀ b))) ◃∎
          foo f p@idp b c h₀ = !ₛ $
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
          step₅' :
            homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h) ◃∙
            ap (λ k → k (λ y → idp))
               (transp-naturality {B = λ x → ∀ y → cp₁₁ x y == [ north ]₂} {C = λ x → cp₁₁ x embase == cp₁₁ x embase}
                                  (λ h → h embase ∙ ! (h embase)) (emloop g)) ◃∎
            =ₛ
            ap-cst [ north ]₂ (emloop h) ◃∙
            ! (!-inv-r (h₁ embase)) ◃∙
            ! (ap (λ v → h₁ v ∙ ! (h₁ embase)) (emloop h)) ◃∙
            !-inv-r (h₁ embase) ◃∙
            ! (transp-idp (λ a → cp₁₁ a embase) (emloop g)) ◃∎
          step₅' =
            homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h) ◃∙
            app= (transp-naturality {B = λ x → ∀ y → cp₁₁ x y == [ north ]₂} {C = λ x → cp₁₁ x embase == cp₁₁ x embase}
                                    (λ h → h embase ∙ ! (h embase)) (emloop g))
                 (λ y → idp) ◃∎
              =ₛ⟨ 1 & 1 & foo cp₁₁ (emloop g) embase [ north ]₂ (λ y → idp) ⟩
            homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h) ◃∙
            !-inv-r (h₁ embase) ◃∙
            ! (transp-idp (λ a → cp₁₁ a embase) (emloop g)) ◃∙
            idp ◃∎
              =ₛ⟨ 3 & 1 & expand [] ⟩
            homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h) ◃∙
            !-inv-r (h₁ embase) ◃∙
            ! (transp-idp (λ a → cp₁₁ a embase) (emloop g)) ◃∎
              =ₛ⟨ 1 & 0 & !ₛ $ seq-!-inv-r (ap (λ v → h₁ v ∙ ! (h₁ embase)) (emloop h) ◃∙ !-inv-r (h₁ embase) ◃∎) ⟩
            homotopy-naturality-to-cst (λ y → [ north ]₂) [ north ]₂ h₁ (emloop h) ◃∙
            ap (λ v → h₁ v ∙ ! (h₁ embase)) (emloop h) ◃∙
            !-inv-r (h₁ embase) ◃∙
            ! (!-inv-r (h₁ embase)) ◃∙
            ! (ap (λ v → h₁ v ∙ ! (h₁ embase)) (emloop h)) ◃∙
            !-inv-r (h₁ embase) ◃∙
            ! (transp-idp (λ a → cp₁₁ a embase) (emloop g)) ◃∎
              =ₛ⟨ 0 & 3 & homotopy-naturality-cst-to-cst' [ north ]₂ [ north ]₂ h₁ (emloop h) ⟩
            ap-cst [ north ]₂ (emloop h) ◃∙
            ! (!-inv-r (h₁ embase)) ◃∙
            ! (ap (λ v → h₁ v ∙ ! (h₁ embase)) (emloop h)) ◃∙
            !-inv-r (h₁ embase) ◃∙
            ! (transp-idp (λ a → cp₁₁ a embase) (emloop g)) ◃∎ ∎ₛ

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
          =⟨ vert-degen-square-∙v⊡ (ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h)) _  ⟩
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
        EM₁Level₁DoublePathElim R₊ R₊ {C = EM 2} {{Trunc-level}}
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
