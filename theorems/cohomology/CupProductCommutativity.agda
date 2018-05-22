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

    cp₁₁-comm : ∀ x y → cp₁₁ x y == antipodal-map (cp₁₁ y x)
    cp₁₁-comm x y =
      EM₁-level₁-elim {P = λ x → P x y}
                      {{λ x → P-level x y}}
                      (CommEmbaseElim.f y)
                      {!!}
                      {!!}
                      x
