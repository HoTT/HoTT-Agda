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
      P : EM₁ R₊ → EM₁ R₊ → Type i
      P x y = cp₁₁ x y == antipodal-map (cp₁₁ y x)

      P-level : (x y : EM₁ R₊) → has-level 1 (P x y)
      P-level x y = has-level-apply (EM-level 2) _ _

      comm-embase-emloop' : ∀ g
        → ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop g) ==
          ap (cp₁₁ embase) (emloop g)
      comm-embase-emloop' g = ↯
        ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop g)
          =⟪ ap-∘ (λ f → antipodal-map (f embase)) cp₁₁ (emloop g) ⟫
        ap (λ f → antipodal-map (f embase)) (ap cp₁₁ (emloop g))
          =⟪ ap-∘ antipodal-map (λ f → f embase) (ap cp₁₁ (emloop g)) ⟫
        ap antipodal-map (app= (ap cp₁₁ (emloop g)) embase)
          =⟪ ap (ap antipodal-map) (app=-ap-cp₁₁ g embase) ⟫
        ap antipodal-map (ap [_] (η (cp₀₁ g embase)))
          =⟪idp⟫
        ap antipodal-map (ap [_] (η embase))
          =⟪ ap (ap antipodal-map ∘ ap [_]) (!-inv-r (merid embase)) ⟫
        ap antipodal-map (ap [_] (idp {a = north}))
          =⟪idp⟫
        idp
          =⟪ ! (ap-cst [ north ] (emloop g)) ⟫
        ap (cst [ north ]) (emloop g)
          =⟪idp⟫
        ap (cp₁₁ embase) (emloop g) ∎∎

      abstract
        comm-embase-emloop-comp' : ∀ g₁ g₂
          → comm-embase-emloop' (R.add g₁ g₂) ∙
            ap (ap (λ z₁ → cp₁₁ embase z₁)) (emloop-comp g₁ g₂)
            ==
            ap (ap (λ z → antipodal-map (cp₁₁ z embase))) (emloop-comp g₁ g₂) ∙'
            ↓-='-in'-∙ {f = λ z → cp₁₁ embase z} {g = λ z → antipodal-map (cp₁₁ z embase)}
                       {p = emloop g₁} {p' = emloop g₂}
                       idp idp idp (comm-embase-emloop' g₁) (comm-embase-emloop' g₂)
        comm-embase-emloop-comp' g₁ g₂ =
          {!!}

      abstract
        comm-embase-emloop : ∀ g → idp == idp [ P embase ↓ emloop g ]
        comm-embase-emloop g =
          ↓-='-in' {f = cp₁₁ embase}
                   {g = λ y → antipodal-map (cp₁₁ y embase)}
                   {p = emloop g}
                   {u = idp}
                   {v = idp}
                   (comm-embase-emloop' g)

        comm-embase-emloop-β : ∀ g →
          comm-embase-emloop g == ↓-='-in' (comm-embase-emloop' g)
        comm-embase-emloop-β g = idp

        comm-embase-emloop-comp : ∀ g₁ g₂ →
          comm-embase-emloop (Group.comp R₊ g₁ g₂)
          ==
          comm-embase-emloop g₁ ∙ᵈ comm-embase-emloop g₂
            [ (λ p → idp == idp [ P embase ↓ p ]) ↓ emloop-comp g₁ g₂ ]
        comm-embase-emloop-comp g₁ g₂ =
          ↓-='-in'-weird {f = λ z → cp₁₁ embase z}
                         {g = λ z → antipodal-map (cp₁₁ z embase)}
                         (emloop-comp g₁ g₂)
                         {u = idp} {v = idp} {w = idp}
                         (comm-embase-emloop' g₁)
                         (comm-embase-emloop' g₂)
                         (comm-embase-emloop' (R.add g₁ g₂))
                         (comm-embase-emloop-comp' g₁ g₂)

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

      comm-emloop-embase' :
        ap (antipodal-map ∘ cp₁₁ embase) (emloop g) ==
        ap (λ x → cp₁₁ x embase) (emloop g)
      comm-emloop-embase' = ↯ comm-emloop-embase↯

      abstract
        comm-emloop-embase : idp == idp [ (λ x → P x embase) ↓ emloop g ]
        comm-emloop-embase = ↓-='-in' {u = idp} {v = idp} comm-emloop-embase'

    module _ (g₁ g₂ : R.El) where
      abstract
        comm-emloop-comp-embase' :
          comm-emloop-embase' (R.add g₁ g₂) ∙
          ap (ap (λ z → cp₁₁ z embase)) (emloop-comp g₁ g₂)
          ==
          ap (ap (λ z → antipodal-map (cp₁₁ embase z))) (emloop-comp g₁ g₂) ∙'
          ↓-='-in'-∙ {f = λ z → cp₁₁ z embase} {g = λ z → antipodal-map (cp₁₁ embase z)}
                     {p = emloop g₁} {p' = emloop g₂}
                     idp idp idp (comm-emloop-embase' g₁) (comm-emloop-embase' g₂)
        comm-emloop-comp-embase' =
          {!!}

      abstract
        comm-emloop-comp-embase :
          comm-emloop-embase (R.add g₁ g₂) ==
          comm-emloop-embase g₁ ∙ᵈ comm-emloop-embase g₂
            [ (λ p → idp == idp [ (λ x → P x embase) ↓ p ]) ↓ emloop-comp g₁ g₂ ]
        comm-emloop-comp-embase =
          ↓-='-in'-weird {f = λ z → cp₁₁ z embase}
                         {g = λ z → antipodal-map (cp₁₁ embase z)}
                         (emloop-comp g₁ g₂)
                         {u = idp} {v = idp} {w = idp}
                         (comm-emloop-embase' g₁)
                         (comm-emloop-embase' g₂)
                         (comm-emloop-embase' (R.add g₁ g₂))
                         comm-emloop-comp-embase'

    abstract
      comm-emloop-emloop : ∀ g h →
        ↓-ap-in (λ Z → Z) (λ a → P a embase) (comm-emloop-embase g) ∙'ᵈ
        ↓-ap-in (λ Z → Z) (P embase) (comm-embase-emloop h)
        ==
        ↓-ap-in (λ Z → Z) (P embase) (comm-embase-emloop h) ∙ᵈ
        ↓-ap-in (λ Z → Z) (λ a → P a embase) (comm-emloop-embase g)
          [ (λ p → PathOver (λ Z → Z) p idp idp) ↓ ap-comm P (emloop g) (emloop h) ]
      comm-emloop-emloop = {!!}
      {-
      comm-emloop-emloop' : ∀ h →
        comm-emloop-embase' ◃
        apd (λ y → ap (λ x → cp₁₁ x y) (emloop g) ∙' comm-embase-elim y) (emloop h)
        ==
        apd (λ y → comm-embase-elim y ∙ ap (λ x → antipodal-map (cp₁₁ y x)) (emloop g)) (emloop h) ▹
        comm-emloop-embase'
      comm-emloop-emloop' h =
        comm-emloop-embase' ◃
        apd (λ y → ap (λ x → cp₁₁ x y) (emloop g) ∙' comm-embase-elim y) (emloop h)
          =⟨ ap (λ w → comm-emloop-embase' ◃ w)
                (apd∙' (λ y → ap (λ x → cp₁₁ x y) (emloop g))
                        comm-embase-elim
                        (emloop h)) ⟩
        comm-emloop-embase' ◃
        apd (λ y → ap (λ x → cp₁₁ x y) (emloop g)) (emloop h) ∙'2ᵈ
        apd comm-embase-elim (emloop h)
        =⟨ ap (λ w → comm-emloop-embase' ◃ w ∙'2ᵈ apd comm-embase-elim (emloop h))
              (apd=↓-cst-in-ap (λ y → ap (λ x → cp₁₁ x y) (emloop g))
                                (emloop h)) ⟩
        comm-emloop-embase' ◃
        ↓-cst-in (ap (λ y → ap (λ x → cp₁₁ x y) (emloop g)) (emloop h)) ∙'2ᵈ
        apd comm-embase-elim (emloop h)
          =⟨ ◃-∙'2ᵈ {x = λ _ → [ north ]}
                    {y = λ y → cp₁₁ embase y}
                    {z = λ y → antipodal-map (cp₁₁ y embase)}
                    {p = idp} {p' = emloop' R₊ h}
                    {q0 = ap (antipodal-map ∘ cp₁₁ embase) (emloop g)}
                    {q0' = ap (λ z → cp₁₁ z embase) (emloop g)}
                    {r0 = idp {a = [ north ]}}
                    {r0' = idp {a = [ north ]}}
                    {q0'' = ap (λ z → cp₁₁ z embase) (emloop g)}
                    {r0'' = idp {a = [ north ]}}
                    comm-emloop-embase'
                    idp
                    (apd (λ y → ap (λ x → cp₁₁ x y) (emloop g)) (emloop h))
                    (apd comm-embase-elim (emloop h)) ⟩
        (comm-emloop-embase' ◃
          apd (λ y → ap (λ x → cp₁₁ x y) (emloop g)) (emloop h)) ∙'2ᵈ
        (idp {a = idp} ◃ apd comm-embase-elim (emloop h))
          =⟨ ap ((comm-emloop-embase' ◃ apd (λ y → ap (λ x → cp₁₁ x y) (emloop g)) (emloop h)) ∙'2ᵈ_)
                (idp◃ (apd comm-embase-elim (emloop h))) ⟩
        (comm-emloop-embase' ◃
          apd (λ y → ap (λ x → cp₁₁ x y) (emloop g)) (emloop h)) ∙'2ᵈ
        apd comm-embase-elim (emloop h)
          =⟨ ap (_∙'2ᵈ apd comm-embase-elim (emloop h)) step₁ ⟩
        ((↯ (3 -#) comm-emloop-embase↯) ◃
          apd (λ y → app= (ap cp₁₁ (emloop g)) y) (emloop h) ▹
          ∘-ap (λ f → f embase) cp₁₁ (emloop g)) ∙'2ᵈ
        apd comm-embase-elim (emloop h)
          =⟨ ap (((↯ (3 -#) comm-emloop-embase↯) ◃
                  apd (λ y → app= (ap cp₁₁ (emloop g)) y) (emloop h) ▹
                  ∘-ap (λ f → f embase) cp₁₁ (emloop g)) ∙'2ᵈ_)
                (comm-embase-elim-emloop-β h) ⟩
        ((↯ (3 -#) comm-emloop-embase↯) ◃
          apd (λ y → app= (ap cp₁₁ (emloop g)) y) (emloop h) ▹
          ∘-ap (λ f → f embase) cp₁₁ (emloop g)) ∙'2ᵈ
        ↓-='-in' {u = idp} {v = idp} (comm-embase-emloop' h)
        -}
        {-
          =⟨ ? ⟩
        comm-emloop-embase ◃
        apd (λ y → ap [_] (η (cp₀₁ g y))) (emloop h) ∙'2ᵈ
        ↓-='-in' (comm-embase-emloop h)
          =⟨ ? ⟩
        comm-emloop-embase ◃
        ↓-cst-in (ap (λ y → ap [_] (η (cp₀₁ g y))) (emloop h)) ∙'2ᵈ
        ↓-='-in' (comm-embase-emloop h)
          =⟨ ? ⟩
          =⟨ {!λ y → ap (λ x → antipodal-map (cp₁₁ y x)) (emloop g)!} ⟩
        (apd comm-embase-elim (emloop h) ∙2ᵈ
          apd (λ y → ap (λ x → antipodal-map (cp₁₁ y x)) (emloop g)) (emloop h)) ▹
        comm-emloop-embase'
          =⟨ ap (λ w → w ▹ comm-emloop-embase')
                (! (apd∙ comm-embase-elim
                        (λ y → ap (λ x → antipodal-map (cp₁₁ y x)) (emloop g))
                        (emloop h))) ⟩
        apd (λ y → comm-embase-elim y ∙ ap (λ x → antipodal-map (cp₁₁ y x)) (emloop g)) (emloop h) ▹
        comm-emloop-embase' =∎
        where
          step₁ : comm-emloop-embase' ◃
                  apd (λ y → ap (λ x → cp₁₁ x y) (emloop g)) (emloop h)
                  ==
                  (↯ (3 -#) comm-emloop-embase↯) ◃
                  apd (λ y → app= (ap cp₁₁ (emloop g)) y) (emloop h) ▹
                  ∘-ap (λ f → f embase) cp₁₁ (emloop g)
          step₁ =
            comm-emloop-embase' ◃
            apd (λ y → ap (λ x → cp₁₁ x y) (emloop g)) (emloop h)
              =⟨ ap (λ w → w ◃ apd (λ y → ap (λ x → cp₁₁ x y) (emloop g)) (emloop h))
                    (↯-#-! comm-emloop-embase↯ 3) ⟩
            ((↯ (3 -#) comm-emloop-embase↯) ∙
              ∘-ap (λ f → f embase) cp₁₁ (emloop g)) ◃
            apd (λ y → ap (λ x → cp₁₁ x y) (emloop g)) (emloop h)
              =⟨ ∙ᵈ-assoc {e₀₁ = idp} {e₁₂ = idp} {e₂₃ = emloop h}
                          (↯ (3 -#) comm-emloop-embase↯)
                          (∘-ap (λ f → f embase) cp₁₁ (emloop g))
                          (apd (λ y → ap (λ x → cp₁₁ x y) (emloop g)) (emloop h)) ⟩
            (↯ (3 -#) comm-emloop-embase↯) ◃
            ∘-ap (λ f → f embase) cp₁₁ (emloop g) ◃
            apd (λ y → ap (λ x → cp₁₁ x y) (emloop g)) (emloop h)
              =⟨ ap ((↯ (3 -#) comm-emloop-embase↯) ◃_) $ ! $
                  homotopy-naturality' (λ y → app= (ap cp₁₁ (emloop g)) y)
                                      (λ y → ap (λ x → cp₁₁ x y) (emloop g))
                                      (λ y → ∘-ap (λ f → f y) cp₁₁ (emloop g))
                                      (emloop h) ⟩
            (↯ (3 -#) comm-emloop-embase↯) ◃
            apd (λ y → app= (ap cp₁₁ (emloop g)) y) (emloop h) ▹
            ∘-ap (λ f → f embase) cp₁₁ (emloop g) =∎
            -}

    private
      module CP₁₁Comm =
        EM₁Level₁DoubleElim R₊ R₊ {P = P} {{P-level}}
          idp
          comm-embase-emloop
          comm-emloop-embase
          comm-embase-emloop-comp
          comm-emloop-comp-embase
          comm-emloop-emloop

    abstract
      cp₁₁-comm : ∀ x y → cp₁₁ x y == antipodal-map (cp₁₁ y x)
      cp₁₁-comm = CP₁₁Comm.f
