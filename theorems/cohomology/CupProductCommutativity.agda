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

      comm-embase-ap : ∀ g
        → ap (λ z → antipodal-map (cp₁₁ z embase)) (emloop' R₊ g) ==
          ap (λ z → cp₁₁ embase z) (emloop' R₊ g)
      comm-embase-ap g =
        ap (λ y → antipodal-map (cp₁₁ y embase)) (emloop g)
          =⟨ ap-∘ (λ f → antipodal-map (f embase)) cp₁₁ (emloop g) ⟩
        ap (λ f → antipodal-map (f embase)) (ap cp₁₁ (emloop g))
          =⟨ ap-∘ antipodal-map (λ f → f embase) (ap cp₁₁ (emloop g)) ⟩
        ap antipodal-map (app= (ap cp₁₁ (emloop g)) embase)
          =⟨ ap (ap antipodal-map) (app=-ap-cp₁₁ g embase) ⟩
        ap antipodal-map (ap [_] (η embase))
          =⟨ ap (ap antipodal-map ∘ ap [_]) (!-inv-r (merid embase)) ⟩
        idp
          =⟨ ! (ap-cst [ north ] (emloop g)) ⟩
        ap (cst [ north ]) (emloop g) =∎

    module CommEmbaseElim =
      EM₁Level₁Elim {P = P embase} {{P-level embase}}
                    idp
                    (λ g → ↓-='-in' (comm-embase-ap g))
                    {!!}

    comm-embase-elim = CommEmbaseElim.f

    private
      P' : EM₁ R₊ → embase' R₊ == embase → Type i
      P' y p = comm-embase-elim y == comm-embase-elim y [ (λ x → P x y) ↓ p ]
      P'-level : ∀ y p → has-level 0 (P' y p)
      P'-level y p = ↓-level (P-level embase y)

    module _ (g : R.El) where
      module CommEmloopElim =
        EM₁SetElim {P = λ y → P' y (emloop g) }
                   {{λ y → P'-level y (emloop g)}}
                   {!!}
                   {!!}

      comm-emloop-elim = CommEmloopElim.f

    module _ (g₁ g₂ : R.El) where
      private
        P'' : EM₁ R₊ → Type i
        P'' y = comm-emloop-elim (R.add g₁ g₂) y ==
                comm-emloop-elim g₁ y ∙ᵈ comm-emloop-elim g₂ y [ P' y ↓ emloop-comp g₁ g₂ ]
        P''-level : ∀ y → has-level -1 (P'' y)
        P''-level y = ↓-level (P'-level y (emloop g₁ ∙ emloop g₂))

      module CommEmloopCompElim =
        EM₁PropElim {P = P''} {{P''-level}}
                    {!!}

      comm-emloop-comp-elim = CommEmloopCompElim.f

    cp₁₁-comm : ∀ x y → cp₁₁ x y == antipodal-map (cp₁₁ y x)
    cp₁₁-comm x y =
      EM₁-level₁-elim {P = λ x → P x y}
                      {{λ x → P-level x y}}
                      (comm-embase-elim y)
                      (λ g → comm-emloop-elim g y)
                      {!!} -- (λ g₁ g₂ → comm-emloop-comp-elim g₁ g₂ y)
                      x
