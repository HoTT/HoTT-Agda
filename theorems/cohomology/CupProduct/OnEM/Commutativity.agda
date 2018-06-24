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

  antipodal-map : EM 2 → EM 2
  antipodal-map = Trunc-fmap (Susp-fmap EM₁-antipodal-map)

  module CP₁₁-comm where

    abstract

      comm-embase-emloop↯ : ∀ h →
        ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h) =-=
        ap (cp₁₁ embase) (emloop h)
      comm-embase-emloop↯ h =
        ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h)
          =⟪ ap-∘ (λ f → antipodal-map (f embase)) cp₁₁ (emloop h) ⟫
        ap (λ f → antipodal-map (f embase)) (ap cp₁₁ (emloop h))
          =⟪ ap-∘ antipodal-map (λ f → f embase) (ap cp₁₁ (emloop h)) ⟫
        ap antipodal-map (app= (ap cp₁₁ (emloop h)) embase)
          =⟪ ap (ap antipodal-map) (app=-ap-cp₁₁ h embase) ⟫
        ap antipodal-map (ap [_] (η (cp₀₁ h embase)))
          =⟪idp⟫
        ap antipodal-map (ap [_] (η embase))
          =⟪ ap (ap antipodal-map ∘ ap [_]) (!-inv-r (merid embase)) ⟫
        ap antipodal-map (ap [_] (idp {a = north}))
          =⟪idp⟫
        idp
          =⟪ ! (ap-cst [ north ] (emloop h)) ⟫
        ap (cst [ north ]) (emloop h)
          =⟪idp⟫
        ap (cp₁₁ embase) (emloop h) ∎∎

      comm-emloop-embase↯ : ∀ g →
        ap (λ x → cp₁₁ x embase) (emloop g) =-=
        ap (antipodal-map ∘ cp₁₁ embase) (emloop g)
      comm-emloop-embase↯ g =
        ap (λ x → cp₁₁ x embase) (emloop g)
          =⟪ ap-cp₁₁ g embase ⟫
        ap [_] (η (cp₀₁ g embase))
          =⟪idp⟫
        ap [_] (η embase)
          =⟪ ap (ap [_]) (!-inv-r (merid embase)) ⟫
        idp
          =⟪ ! (ap-cst [ north ] (emloop g)) ⟫
        ap (cst [ north ]) (emloop g) ∎∎

      comm-embase-emloop' : ∀ h →
        ap (λ y → cp₁₁ embase y) (emloop h) ==
        ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h)
      comm-embase-emloop' h = ! (↯ (comm-embase-emloop↯ h))

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
        {!!}

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
        ap-cp₁₁ (R.add g₁ g₂) embase ◃∙
        ap (ap [_]) (!-inv-r (merid embase)) ◃∙
        ! (ap-cst [ north ] (emloop (R.add g₁ g₂))) ◃∙
        ap (ap (λ x → antipodal-map (cp₁₁ embase x))) (emloop-comp g₁ g₂) ◃∎
          =ₛ⟨ 2 & 2 & !ₛ $
              homotopy-naturality
                (λ _ → idp)
                (ap (cst [ north ]))
                (λ p → ! (ap-cst [ north ] p))
                (emloop-comp g₁ g₂) ⟩
        ap-cp₁₁ (R.add g₁ g₂) embase ◃∙
        ap (ap [_]) (!-inv-r (merid embase)) ◃∙
        ap (λ _ → idp) (emloop-comp g₁ g₂) ◃∙
        ! (ap-cst [ north ] (emloop g₁ ∙ emloop g₂)) ◃∎
          =ₛ⟨ 2 & 1 & =ₛ-in {t = []} (ap-cst idp (emloop-comp g₁ g₂)) ⟩
        ap-cp₁₁ (R.add g₁ g₂) embase ◃∙
        ap (ap [_]) (!-inv-r (merid embase)) ◃∙
        ! (ap-cst [ north ] (emloop g₁ ∙ emloop g₂)) ◃∎
          =ₛ⟨ 1 & 1 & !ₛ (app=-F₀₄-pres-comp-embase-coh g₁ g₂) ⟩
        ap-cp₁₁ (R.add g₁ g₂) embase ◃∙
        app= (TwoSemiFunctor.pres-comp F₀₄ g₁ g₂) embase ◃∙
        ap2 _∙_ (ap (ap [_]) (!-inv-r (merid embase))) (ap (ap [_]) (!-inv-r (merid embase))) ◃∙
        ! (ap-cst [ north ] (emloop g₁ ∙ emloop g₂)) ◃∎
          =ₛ⟨ 0 & 2 & !ₛ (ap-cp₁₁-coh g₁ g₂ embase) ⟩
        ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ◃∙
        ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂) ◃∙
        ap2 _∙_ (ap-cp₁₁ g₁ embase) (ap-cp₁₁ g₂ embase) ◃∙
        ap2 _∙_ (ap (ap [_]) (!-inv-r (merid embase))) (ap (ap [_]) (!-inv-r (merid embase))) ◃∙
        ! (ap-cst [ north ] (emloop g₁ ∙ emloop g₂)) ◃∎
          =ₛ⟨ 4 & 1 &
              !-=ₛ $
              =ₛ-in {s = ap-cst [ north ] (emloop g₁ ∙ emloop g₂) ◃∎}
                    {t = ap-∙ (cst [ north ]) (emloop g₁) (emloop g₂) ◃∙
                         ap2 _∙_ (ap-cst [ north ] (emloop g₁))
                                 (ap-cst [ north ] (emloop g₂)) ◃∎} $
              ap-cst-coh [ north ] (emloop g₁) (emloop g₂) ⟩
        ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ◃∙
        ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂) ◃∙
        ap2 _∙_ (ap-cp₁₁ g₁ embase) (ap-cp₁₁ g₂ embase) ◃∙
        ap2 _∙_ (ap (ap [_]) (!-inv-r (merid embase))) (ap (ap [_]) (!-inv-r (merid embase))) ◃∙
        ! (ap2 _∙_ (ap-cst [ north ] (emloop g₁)) (ap-cst [ north ] (emloop g₂))) ◃∙
        ! (ap-∙ (cst [ north ]) (emloop g₁) (emloop g₂)) ◃∎
          =ₛ₁⟨ 4 & 1 & ! (ap2-! _∙_ (ap-cst [ north ] (emloop g₁)) (ap-cst [ north ] (emloop g₂))) ⟩
        ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ◃∙
        ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂) ◃∙
        ap2 _∙_ (ap-cp₁₁ g₁ embase) (ap-cp₁₁ g₂ embase) ◃∙
        ap2 _∙_ (ap (ap [_]) (!-inv-r (merid embase))) (ap (ap [_]) (!-inv-r (merid embase))) ◃∙
        ap2 _∙_ (! (ap-cst [ north ] (emloop g₁))) (! (ap-cst [ north ] (emloop g₂))) ◃∙
        ! (ap-∙ (cst [ north ]) (emloop g₁) (emloop g₂)) ◃∎
          =ₛ⟨ 2 & 3 & ∙-ap2-seq _∙_ (comm-emloop-embase↯ g₁) (comm-emloop-embase↯ g₂) ⟩
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
        {!!}

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
