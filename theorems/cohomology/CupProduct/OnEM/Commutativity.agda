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

    private
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

      comm-embase-emloop : ∀ h →
        Square idp
               (ap (cp₁₁ embase) (emloop h))
               (ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop h))
               idp
      comm-embase-emloop h = vert-degen-square (! (↯ comm-embase-emloop↯ h))

    module _ (g : R.El) where
      comm-emloop-embase↯ :
        ap (antipodal-map ∘ cp₁₁ embase) (emloop g) =-=
        ap (λ x → cp₁₁ x embase) (emloop g)
      comm-emloop-embase↯ =
        ap (cst [ north ]) (emloop g)
          =⟪ ap-cst [ north ] (emloop g) ⟫
        idp
          =⟪ ! (ap (ap [_]) (!-inv-r (merid embase))) ⟫
        ap [_] (η embase)
          =⟪idp⟫
        ap [_] (η (cp₀₁ g embase))
          =⟪ ! (app=-ap-cp₁₁ g embase) ⟫
        app= (ap cp₁₁ (emloop g)) embase
          =⟪ ∘-ap (λ f → f embase) cp₁₁ (emloop g) ⟫
        ap (λ x → cp₁₁ x embase) (emloop g) ∎∎

      comm-emloop-embase :
        Square idp
               (ap (λ x → cp₁₁ x embase) (emloop g))
               (ap (λ x → antipodal-map (cp₁₁ embase x)) (emloop g))
               idp
      comm-emloop-embase = vert-degen-square (! (↯ comm-emloop-embase↯))

    abstract
      comm-embase-emloop-comp : ∀ h₁ h₂ →
        comm-embase-emloop (Group.comp R₊ h₁ h₂) ⊡v∙
        ap (ap (λ y → antipodal-map (cp₁₁ y embase))) (emloop-comp' R₊ h₁ h₂)
        ==
        ap (ap (λ y → cp₁₁ embase y)) (emloop-comp' R₊ h₁ h₂) ∙v⊡
        ↓-='-square-comp (comm-embase-emloop h₁) (comm-embase-emloop h₂)
      comm-embase-emloop-comp h₁ h₂ =
        {!!}

    abstract
      comm-emloop-comp-embase : ∀ g₁ g₂ →
        comm-emloop-embase (Group.comp R₊ g₁ g₂) ⊡v∙
        ap (ap (λ x → antipodal-map (cp₁₁ embase x))) (emloop-comp' R₊ g₁ g₂)
        ==
        ap (ap (λ x → cp₁₁ x embase)) (emloop-comp' R₊ g₁ g₂) ∙v⊡
        ↓-='-square-comp (comm-emloop-embase g₁) (comm-emloop-embase g₂)
      comm-emloop-comp-embase g₁ g₂ =
        {!!}

    abstract
      comm-emloop-emloop : ∀ g h →
        ap-comm (λ x y → cp₁₁ x y) (emloop g) (emloop h) ∙v⊡
        comm-embase-emloop h ⊡h comm-emloop-embase g
        ==
        (comm-emloop-embase g ⊡h comm-embase-emloop h) ⊡v∙
        ap-comm (λ x y → antipodal-map (cp₁₁ y x)) (emloop g) (emloop h)
      comm-emloop-emloop g h =
        {!!}

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
