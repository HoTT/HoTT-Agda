{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane

module cohomology.CupProductCommutativity {i} (R : CRing i) where

  open import cohomology.CupProduct R
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

      comm-embase-emloop : ∀ g
        → ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop g) ==
          ap (cp₁₁ embase) (emloop g)
      comm-embase-emloop g = ↯
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
        comm-embase-emloop-comp : ∀ g₁ g₂
          → comm-embase-emloop (R.add g₁ g₂) ∙
            ap (ap (λ z₁ → cp₁₁ embase z₁)) (emloop-comp g₁ g₂)
            ==
            ap (ap (λ z → antipodal-map (cp₁₁ z embase))) (emloop-comp g₁ g₂) ∙'
            ↓-='-in'-∙ {f = λ z → cp₁₁ embase z} {g = λ z → antipodal-map (cp₁₁ z embase)}
                      {p = emloop g₁} {p' = emloop g₂}
                      idp idp idp (comm-embase-emloop g₁) (comm-embase-emloop g₂)
        comm-embase-emloop-comp g₁ g₂ =
          {!!}

    module CommEmbaseElim =
      EM₁Level₁Elim {P = P embase} {{P-level embase}}
                    idp
                    (λ g → ↓-='-in' (comm-embase-emloop g))
                    (λ g₁ g₂ → ↓-='-in'-weird {f = λ z → cp₁₁ embase z}
                                              {g = λ z → antipodal-map (cp₁₁ z embase)}
                                              (emloop-comp g₁ g₂)
                                              {u = idp} {v = idp} {w = idp}
                                              (comm-embase-emloop g₁)
                                              (comm-embase-emloop g₂)
                                              (comm-embase-emloop (R.add g₁ g₂))
                                              (comm-embase-emloop-comp g₁ g₂))

    comm-embase-elim = CommEmbaseElim.f

    private
      P' : EM₁ R₊ → embase' R₊ == embase → Type i
      P' y p = comm-embase-elim y == comm-embase-elim y [ (λ x → P x y) ↓ p ]
      P'-level : ∀ y p → has-level 0 (P' y p)
      P'-level y p = ↓-level (P-level embase y)

    module _ (g : R.El) where
      comm-emloop-embase :
        ap (antipodal-map ∘ cp₁₁ embase) (emloop g) ==
        ap (λ z → cp₁₁ z embase) (emloop g)
      comm-emloop-embase = ↯
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
        ap (λ z → cp₁₁ z embase) (emloop g) ∎∎

      module CommEmloopElim =
        EM₁SetElim {P = λ y → P' y (emloop g) }
                   {{λ y → P'-level y (emloop g)}}
                   (↓-='-in' {u = idp} {v = idp} comm-emloop-embase)
                   (λ g → ap↓ ↓-='-in' {!↓-='-in' {f = λ y → comm-embase-elim y ∙ ap (λ x → antipodal-map (cp₁₁ y x)) (emloop g)}
                                                 {g = λ y → ap (λ x → cp₁₁ x y) (emloop g) ∙' comm-embase-elim y}
                                                 ?!})

      comm-emloop-elim = CommEmloopElim.f

    module _ (g₁ g₂ : R.El) where
      private
        P'' : EM₁ R₊ → Type i
        P'' y = comm-emloop-elim (R.add g₁ g₂) y ==
                comm-emloop-elim g₁ y ∙ᵈ comm-emloop-elim g₂ y [ P' y ↓ emloop-comp g₁ g₂ ]
        P''-level : ∀ y → has-level -1 (P'' y)
        P''-level y = ↓-level (P'-level y (emloop g₁ ∙ emloop g₂))

      abstract
        comm-emloop-comp-embase :
          comm-emloop-embase (R.add g₁ g₂) ∙
          ap (ap (λ z → cp₁₁ z embase)) (emloop-comp g₁ g₂)
          ==
          ap (ap (λ z → antipodal-map (cp₁₁ embase z))) (emloop-comp g₁ g₂) ∙'
          ↓-='-in'-∙ {f = λ z → cp₁₁ z embase} {g = λ z → antipodal-map (cp₁₁ embase z)}
                    {p = emloop g₁} {p' = emloop g₂}
                    idp idp idp (comm-emloop-embase g₁) (comm-emloop-embase g₂)
        comm-emloop-comp-embase =
          {!!}

      module CommEmloopCompElim =
        EM₁PropElim {P = P''} {{P''-level}}
                    (↓-='-in'-weird {f = λ z → cp₁₁ z embase}
                                    {g = λ z → antipodal-map (cp₁₁ embase z)}
                                    (emloop-comp g₁ g₂)
                                    {u = idp} {v = idp} {w = idp}
                                    (comm-emloop-embase g₁)
                                    (comm-emloop-embase g₂)
                                    (comm-emloop-embase (R.add g₁ g₂))
                                    comm-emloop-comp-embase)

      abstract
        comm-emloop-comp-elim = CommEmloopCompElim.f

    cp₁₁-comm : ∀ x y → cp₁₁ x y == antipodal-map (cp₁₁ y x)
    cp₁₁-comm x y =
      EM₁-level₁-elim {P = λ x → P x y}
                      {{λ x → P-level x y}}
                      (comm-embase-elim y)
                      (λ g → comm-emloop-elim g y)
                      {!!} -- (λ g₁ g₂ → comm-emloop-comp-elim g₁ g₂ y)
                      x
