{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane
open import homotopy.EilenbergMacLane1 using (EM₁-level₁)
open import homotopy.EM1HSpaceAssoc
open import lib.types.TwoSemiCategory
open import lib.two-semi-categories.FunCategory
open import lib.two-semi-categories.FundamentalCategory

module cohomology.CupProduct.OnEM.Definition {i} (R : CRing i) where

  module R = CRing R
  open R using () renaming (add-group to R₊) public

  open EM₁HSpaceAssoc R.add-ab-group hiding (comp-functor) renaming (mult to EM₁-mult) public

  module _ (g : R.El) where
    private
      loop' : R.El → embase' R₊ == embase
      loop' g' = emloop (R.mult g g')

      comp' : (g₁' g₂' : R.El) → loop' (R.add g₁' g₂') == loop' g₁' ∙ loop' g₂'
      comp' g₁' g₂' = ap emloop (R.distr-r g g₁' g₂') ∙ emloop-comp _ _

      module Rec = EM₁Level₁Rec {G = R₊} {C = EM₁ R₊} {{EM₁-level₁ R₊}} embase (group-hom loop' comp')

    abstract
      cp₀₁ : EM₁ R₊ → EM₁ R₊
      cp₀₁ = Rec.f

      cp₀₁-embase-β : cp₀₁ embase ↦ embase
      cp₀₁-embase-β = Rec.embase-β
      {-# REWRITE cp₀₁-embase-β #-}

      cp₀₁-emloop-β : ∀ g' → ap cp₀₁ (emloop g') == emloop (R.mult g g')
      cp₀₁-emloop-β = Rec.emloop-β

  module distr-l (g₁ g₂ : R.El) where

    f : EM₁ R₊ → EM₁ R₊
    f x = cp₀₁ (R.add g₁ g₂) x

    g : EM₁ R₊ → EM₁ R₊
    g x = EM₁-mult (cp₀₁ g₁ x) (cp₀₁ g₂ x)

    base' : f (embase' R₊) == g (embase' R₊)
    base' = idp

    abstract
      loop' : (h : R.El) → base' == base' [ (λ x → f x == g x) ↓ emloop h ]
      loop' h = ↓-='-in {f = f} {g = g} {p = emloop h} {u = base'} {v = base'} $
        base' ∙' ap g (emloop h)
          =⟨ ∙'-unit-l (ap g (emloop h)) ⟩
        ap g (emloop h)
          =⟨ ! (ap2-diag (λ x y → EM₁-mult (cp₀₁ g₁ x) $ cp₀₁ g₂ y) (emloop h)) ⟩
        ap2 (λ x y → EM₁-mult (cp₀₁ g₁ x) $ cp₀₁ g₂ y) (emloop h) (emloop h)
          =⟨ ! (ap2-ap-l (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) (EM₁-mult ∘ cp₀₁ g₁) (emloop h) (emloop h)) ⟩
        ap2 (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) (ap (EM₁-mult ∘ cp₀₁ g₁) (emloop h)) (emloop h)
          =⟨ ap-∘ EM₁-mult (cp₀₁ g₁) (emloop h) |in-ctx (λ z → ap2 (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) z (emloop h)) ⟩
        ap2 (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) (ap EM₁-mult (ap (cp₀₁ g₁) (emloop h))) (emloop h)
          =⟨ cp₀₁-emloop-β g₁ h |in-ctx (λ z → ap2 (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) (ap EM₁-mult z) (emloop h)) ⟩
        ap2 (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) (ap EM₁-mult (emloop (R.mult g₁ h))) (emloop h)
          =⟨ mult-emloop-β (R.mult g₁ h) |in-ctx (λ z → ap2 (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) z (emloop h)) ⟩
        ap2 (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) (mult-loop (R.mult g₁ h)) (emloop h)
          =⟨ ap2-out (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) (mult-loop (R.mult g₁ h)) (emloop h) ⟩
        ap (λ (f : EM₁ R₊ → EM₁ R₊) → f embase) (mult-loop (R.mult g₁ h)) ∙ ap (cp₀₁ g₂) (emloop h)
          =⟨ app=-β (mult-loop' (R.mult g₁ h)) embase |in-ctx (λ z → z ∙ ap (cp₀₁ g₂) (emloop h)) ⟩
        mult-loop' (R.mult g₁ h) embase ∙ ap (cp₀₁ g₂) (emloop h)
          =⟨ idp ⟩
        emloop (R.mult g₁ h) ∙ ap (cp₀₁ g₂) (emloop h)
          =⟨ cp₀₁-emloop-β g₂ h |in-ctx (λ z → emloop (R.mult g₁ h) ∙ z) ⟩
        emloop (R.mult g₁ h) ∙ emloop (R.mult g₂ h)
          =⟨ ! (emloop-comp (R.mult g₁ h) (R.mult g₂ h)) ⟩
        emloop (R.add (R.mult g₁ h) (R.mult g₂ h))
          =⟨ ap emloop (! (R.distr-l g₁ g₂ h)) ⟩
        emloop (R.mult (R.add g₁ g₂) h)
          =⟨ ! (cp₀₁-emloop-β (R.add g₁ g₂) h) ⟩
        ap f (emloop h)
          =⟨ ! (∙-unit-r (ap f (emloop h))) ⟩
        ap f (emloop h) ∙ base' =∎

    cp₀₁-distr-l : (g' : EM₁ R₊) → cp₀₁ (R.add g₁ g₂) g' == EM₁-mult (cp₀₁ g₁ g') (cp₀₁ g₂ g')
    cp₀₁-distr-l =
      EM₁-set-elim
        {P = λ x → f x == g x}
        {{λ x → has-level-apply (EM₁-level₁ R₊) _ _}}
        base' loop'

  open distr-l public using (cp₀₁-distr-l)

  module _ (g₁ g₂ g₃ : R.El) (g' : EM₁ R₊) where

    cp₀₁-distr-l₁ : cp₀₁ (R.add (R.add g₁ g₂) g₃) g' == EM₁-mult (cp₀₁ g₁ g') (EM₁-mult (cp₀₁ g₂ g') (cp₀₁ g₃ g'))
    cp₀₁-distr-l₁ =
      cp₀₁-distr-l (R.add g₁ g₂) g₃ g' ∙
      ap (λ s → EM₁-mult s (cp₀₁ g₃ g')) (cp₀₁-distr-l g₁ g₂ g') ∙
      H-⊙EM₁-assoc (cp₀₁ g₁ g') (cp₀₁ g₂ g') (cp₀₁ g₃ g')

    cp₀₁-distr-l₂ : cp₀₁ (R.add (R.add g₁ g₂) g₃) g' == EM₁-mult (cp₀₁ g₁ g') (EM₁-mult (cp₀₁ g₂ g') (cp₀₁ g₃ g'))
    cp₀₁-distr-l₂ =
      ap (λ s → cp₀₁ s g') (R.add-assoc g₁ g₂ g₃) ∙
      cp₀₁-distr-l g₁ (R.add g₂ g₃) g' ∙
      ap (EM₁-mult (cp₀₁ g₁ g')) (cp₀₁-distr-l g₂ g₃ g')

  abstract
    cp₀₁-distr-l-coh : (g₁ g₂ g₃ : R.El) (g' : EM₁ R₊)
      → cp₀₁-distr-l₁ g₁ g₂ g₃ g' == cp₀₁-distr-l₂ g₁ g₂ g₃ g'
    cp₀₁-distr-l-coh g₁ g₂ g₃ =
      EM₁-prop-elim
        {P = λ g' → cp₀₁-distr-l₁ g₁ g₂ g₃ g' == cp₀₁-distr-l₂ g₁ g₂ g₃ g'}
        {{λ g' → has-level-apply (has-level-apply (EM₁-level₁ R₊) _ _) _ _}}
        (idp
          =⟨ ! (ap-cst embase (R.add-assoc g₁ g₂ g₃)) ⟩
        ap (cst embase) (R.add-assoc g₁ g₂ g₃)
          =⟨ ! (∙-unit-r (ap (cst embase) (R.add-assoc g₁ g₂ g₃))) ⟩
        ap (cst embase) (R.add-assoc g₁ g₂ g₃) ∙ idp =∎)

  group-to-EM₁-endos :
    TwoSemiFunctor
      (group-to-cat R₊)
      (fun-cat (EM₁ R₊) EM₁-2-semi-category)
  group-to-EM₁-endos =
    record
    { F₀ = λ _ _ → unit
    ; F₁ = λ g x → cp₀₁ g x
    ; pres-comp = λ g₁ g₂ → λ= (cp₀₁-distr-l g₁ g₂)
    ; pres-comp-coh = λ g₁ g₂ g₃ → pres-comp-coh g₁ g₂ g₃
      -- TODO: for some reason, this last field takes a really long time to check
      -- it is recommended to comment it out
    }
    where
    abstract
      pres-comp-coh : ∀ g₁ g₂ g₃ →
        λ= (cp₀₁-distr-l (R.add g₁ g₂) g₃) ◃∙
        ap (λ s g' → EM₁-mult (s g') (cp₀₁ g₃ g')) (λ= (cp₀₁-distr-l g₁ g₂)) ◃∙
        λ= (λ g' → H-⊙EM₁-assoc (cp₀₁ g₁ g') (cp₀₁ g₂ g') (cp₀₁ g₃ g')) ◃∎
        =ₛ
        ap (λ s → cp₀₁ s) (R.add-assoc g₁ g₂ g₃) ◃∙
        λ= (cp₀₁-distr-l g₁ (R.add g₂ g₃)) ◃∙
        ap (λ s g' → EM₁-mult (cp₀₁ g₁ g') (s g')) (λ= (cp₀₁-distr-l g₂ g₃)) ◃∎
      pres-comp-coh g₁ g₂ g₃ =
        λ= (cp₀₁-distr-l (R.add g₁ g₂) g₃) ◃∙
        ap (λ s g' → EM₁-mult (s g') (cp₀₁ g₃ g')) (λ= (cp₀₁-distr-l g₁ g₂)) ◃∙
        λ= (λ g' → H-⊙EM₁-assoc (cp₀₁ g₁ g') (cp₀₁ g₂ g') (cp₀₁ g₃ g')) ◃∎
          =ₛ₁⟨ 1 & 1 & λ=-ap (λ g' s → EM₁-mult s (cp₀₁ g₃ g')) (cp₀₁-distr-l g₁ g₂) ⟩
        λ= (cp₀₁-distr-l (R.add g₁ g₂) g₃) ◃∙
        λ= (λ g' → ap (λ s → EM₁-mult s (cp₀₁ g₃ g')) (cp₀₁-distr-l g₁ g₂ g')) ◃∙
        λ= (λ g' → H-⊙EM₁-assoc (cp₀₁ g₁ g') (cp₀₁ g₂ g') (cp₀₁ g₃ g')) ◃∎
          =ₛ⟨ ∙∙-λ= (cp₀₁-distr-l (R.add g₁ g₂) g₃)
                    (λ g' → ap (λ s → EM₁-mult s (cp₀₁ g₃ g')) (cp₀₁-distr-l g₁ g₂ g'))
                    (λ g' → H-⊙EM₁-assoc (cp₀₁ g₁ g') (cp₀₁ g₂ g') (cp₀₁ g₃ g')) ⟩
        λ= (cp₀₁-distr-l₁ g₁ g₂ g₃) ◃∎
          =ₛ₁⟨ ap λ= (λ= (cp₀₁-distr-l-coh g₁ g₂ g₃)) ⟩
        λ= (cp₀₁-distr-l₂ g₁ g₂ g₃) ◃∎
          =ₛ⟨ !ₛ (∙∙-λ= (λ g' → ap (λ s → cp₀₁ s g') (R.add-assoc g₁ g₂ g₃))
                        (cp₀₁-distr-l g₁ (R.add g₂ g₃))
                        (λ g' → ap (EM₁-mult (cp₀₁ g₁ g')) (cp₀₁-distr-l g₂ g₃ g'))) ⟩
        λ= (λ g' → ap (λ s → cp₀₁ s g') (R.add-assoc g₁ g₂ g₃)) ◃∙
        λ= (cp₀₁-distr-l g₁ (R.add g₂ g₃)) ◃∙
        λ= (λ g' → ap (EM₁-mult (cp₀₁ g₁ g')) (cp₀₁-distr-l g₂ g₃ g')) ◃∎
          =ₛ₁⟨ 0 & 1 & ap λ= (λ= (λ g' → ap-∘ (λ f → f g') cp₀₁ (R.add-assoc g₁ g₂ g₃))) ⟩
        λ= (app= (ap (λ s → cp₀₁ s) (R.add-assoc g₁ g₂ g₃))) ◃∙
        λ= (cp₀₁-distr-l g₁ (R.add g₂ g₃)) ◃∙
        λ= (λ g' → ap (EM₁-mult (cp₀₁ g₁ g')) (cp₀₁-distr-l g₂ g₃ g')) ◃∎
          =ₛ₁⟨ 0 & 1 & ! (λ=-η (ap (λ s → cp₀₁ s) (R.add-assoc g₁ g₂ g₃))) ⟩
        ap (λ s → cp₀₁ s) (R.add-assoc g₁ g₂ g₃) ◃∙
        λ= (cp₀₁-distr-l g₁ (R.add g₂ g₃)) ◃∙
        λ= (λ g' → ap (EM₁-mult (cp₀₁ g₁ g')) (cp₀₁-distr-l g₂ g₃ g')) ◃∎
          =ₛ₁⟨ 2 & 1 & ! (λ=-ap (λ g' s → EM₁-mult (cp₀₁ g₁ g') s) (cp₀₁-distr-l g₂ g₃)) ⟩
        ap (λ s → cp₀₁ s) (R.add-assoc g₁ g₂ g₃) ◃∙
        λ= (cp₀₁-distr-l g₁ (R.add g₂ g₃)) ◃∙
        ap (λ s g' → EM₁-mult (cp₀₁ g₁ g') (s g')) (λ= (cp₀₁-distr-l g₂ g₃)) ◃∎ ∎ₛ

  comp-functor :
    TwoSemiFunctor
      EM₁-2-semi-category
      (dual-cat (=ₜ-fundamental-cat (Susp (EM₁ R₊))))
  comp-functor =
    record
    { F₀ = λ _ → [ north ]
    ; F₁ = λ x → [ η x ]
    ; pres-comp = comp
    ; pres-comp-coh = comp-coh
    }
    -- this is *exactly* the same as
    --   `EM₁HSpaceAssoc.comp-functor (R.add-ab-group)`
    -- inlined but Agda chokes on this shorter definition

  group-to-EM₁→EM₂-op :
    TwoSemiFunctor
      (group-to-cat R₊)
      (dual-cat (fun-cat (EM₁ R₊) (=ₜ-fundamental-cat (Susp (EM₁ R₊)))))
  group-to-EM₁→EM₂-op =
    group-to-EM₁-endos –F→
    fun-functor-map (EM₁ R₊) comp-functor –F→
    swap-fun-dual-functor (EM₁ R₊) (=ₜ-fundamental-cat (Susp (EM₁ R₊)))

  module CP₁₁ where

    open EMExplicit R.add-ab-group

    private
      C : Type i
      C = EM₁ R₊ → EM 2

      C-level : has-level 2 C
      C-level = Π-level (λ _ → EM-level 2)

      F' : TwoSemiFunctor (group-to-cat R₊) (fun-cat (EM₁ R₊) (2-type-fundamental-cat (EM 2)))
      F' =
        ab-group-cat-to-dual R.add-ab-group –F→
        dual-functor-map group-to-EM₁→EM₂-op –F→
        from-double-dual (fun-cat (EM₁ R₊) (=ₜ-fundamental-cat (Susp (EM₁ R₊)))) –F→
        fun-functor-map (EM₁ R₊) (=ₜ-to-2-type-fundamental-cat (Susp (EM₁ R₊)))

      F : TwoSemiFunctor (group-to-cat R₊) (2-type-fundamental-cat (EM₁ R₊ → EM 2) {{C-level}})
      F = F' –F→ λ=-functor (EM₁ R₊) (EM 2)

      module CP₁₁-Rec = EM₁Rec {G = R₊} {C = C} {{C-level}} F

    abstract
      cp₁₁ : EM₁ R₊ → EM₁ R₊ → EM 2
      cp₁₁ = CP₁₁-Rec.f

      cp₁₁-embase-β : cp₁₁ embase ↦ (λ _ → [ north ])
      cp₁₁-embase-β = CP₁₁-Rec.embase-β
      {-# REWRITE cp₁₁-embase-β #-}

      cp₁₁-emloop-β : ∀ g → ap cp₁₁ (emloop g) == λ= (λ y → ap [_] (η (cp₀₁ g y)))
      cp₁₁-emloop-β g = CP₁₁-Rec.emloop-β g

      app=-ap-cp₁₁-seq : ∀ g y → app= (ap cp₁₁ (emloop g)) y =-= ap [_] (η (cp₀₁ g y))
      app=-ap-cp₁₁-seq g y =
        app= (ap cp₁₁ (emloop g)) y
          =⟪ ap (λ z → app= z y) (cp₁₁-emloop-β g) ⟫
        app= (λ= (λ y₁ → ap [_] (η (cp₀₁ g y₁)))) y
          =⟪ app=-β (λ x → ap [_] (η (cp₀₁ g x))) y ⟫
        ap [_] (η (cp₀₁ g y)) ∎∎

      app=-ap-cp₁₁ : ∀ g y → app= (ap cp₁₁ (emloop g)) y == ap [_] (η (cp₀₁ g y))
      app=-ap-cp₁₁ g y = ↯ app=-ap-cp₁₁-seq g y

      app=-ap-cp₁₁-coh-seq₁ : ∀ g₁ g₂ y →
        app= (ap cp₁₁ (emloop (R.add g₁ g₂))) y =-= ap [_] (η (cp₀₁ g₁ y)) ∙ ap [_] (η (cp₀₁ g₂ y))
      app=-ap-cp₁₁-coh-seq₁ g₁ g₂ y =
        app= (ap cp₁₁ (emloop (R.add g₁ g₂))) y
          =⟪ ap (λ u → app= (ap cp₁₁ u) y) (emloop-comp g₁ g₂) ⟫
        app= (ap cp₁₁ (emloop g₁ ∙ emloop g₂)) y
          =⟪ ap (λ u → app= u y) (ap-∙ cp₁₁ (emloop g₁) (emloop g₂)) ⟫
        app= (ap cp₁₁ (emloop g₁) ∙ ap cp₁₁ (emloop g₂)) y
          =⟪ ap-∙ (λ f → f y) (ap cp₁₁ (emloop g₁)) (ap cp₁₁ (emloop g₂)) ⟫
        app= (ap cp₁₁ (emloop g₁)) y ∙ app= (ap cp₁₁ (emloop g₂)) y
          =⟪ ap2 _∙_ (app=-ap-cp₁₁ g₁ y) (app=-ap-cp₁₁ g₂ y) ⟫
        ap [_] (η (cp₀₁ g₁ y)) ∙ ap [_] (η (cp₀₁ g₂ y)) ∎∎

      app=-ap-cp₁₁-coh-seq₂ : ∀ g₁ g₂ y →
        app= (ap cp₁₁ (emloop (R.add g₁ g₂))) y =-= ap [_] (η (cp₀₁ g₁ y)) ∙ ap [_] (η (cp₀₁ g₂ y))
      app=-ap-cp₁₁-coh-seq₂ g₁ g₂ y =
        app= (ap cp₁₁ (emloop (R.add g₁ g₂))) y
          =⟪ app=-ap-cp₁₁ (R.add g₁ g₂) y ⟫
        ap [_] (η (cp₀₁ (R.add g₁ g₂) y))
          =⟪ app= (TwoSemiFunctor.pres-comp F' g₁ g₂) y ⟫
        ap [_] (η (cp₀₁ g₁ y)) ∙ ap [_] (η (cp₀₁ g₂ y)) ∎∎

      app=-ap-cp₁₁-coh : ∀ g₁ g₂ y →
        app=-ap-cp₁₁-coh-seq₁ g₁ g₂ y =ₛ app=-ap-cp₁₁-coh-seq₂ g₁ g₂ y
      app=-ap-cp₁₁-coh g₁ g₂ y = {!!}

      ap-cp₁₁-seq : ∀ g y → ap (λ x → cp₁₁ x y) (emloop g) =-= ap [_] (η (cp₀₁ g y))
      ap-cp₁₁-seq g y = ap-∘ (λ f → f y) cp₁₁ (emloop g) ◃∙ app=-ap-cp₁₁-seq g y

      ap-cp₁₁ : ∀ g y → ap (λ x → cp₁₁ x y) (emloop g) == ap [_] (η (cp₀₁ g y))
      ap-cp₁₁ g y = ↯ ap-cp₁₁-seq g y

      ap-cp₁₁-coh-seq₁ : ∀ g₁ g₂ y →
        ap (λ x → cp₁₁ x y) (emloop (R.add g₁ g₂)) =-= ap [_] (η (cp₀₁ g₁ y)) ∙ ap [_] (η (cp₀₁ g₂ y))
      ap-cp₁₁-coh-seq₁ g₁ g₂ y =
        ap (λ x → cp₁₁ x y) (emloop (R.add g₁ g₂))
          =⟪ ap (ap (λ x → cp₁₁ x y)) (emloop-comp g₁ g₂) ⟫
        ap (λ x → cp₁₁ x y) (emloop g₁ ∙ emloop g₂)
          =⟪ ap-∙ (λ x → cp₁₁ x y) (emloop g₁) (emloop g₂) ⟫
        ap (λ x → cp₁₁ x y) (emloop g₁) ∙ ap (λ x → cp₁₁ x y) (emloop g₂)
          =⟪ ap2 _∙_ (ap-cp₁₁ g₁ y) (ap-cp₁₁ g₂ y) ⟫
        ap [_] (η (cp₀₁ g₁ y)) ∙ ap [_] (η (cp₀₁ g₂ y)) ∎∎

      ap-cp₁₁-coh-seq₂ : ∀ g₁ g₂ y →
        ap (λ x → cp₁₁ x y) (emloop (R.add g₁ g₂)) =-= ap [_] (η (cp₀₁ g₁ y)) ∙ ap [_] (η (cp₀₁ g₂ y))
      ap-cp₁₁-coh-seq₂ g₁ g₂ y =
        ap (λ x → cp₁₁ x y) (emloop (R.add g₁ g₂))
          =⟪ ap-cp₁₁ (R.add g₁ g₂) y ⟫
        ap [_] (η (cp₀₁ (R.add g₁ g₂) y))
          =⟪ app= (TwoSemiFunctor.pres-comp F' g₁ g₂) y ⟫
        ap [_] (η (cp₀₁ g₁ y)) ∙ ap [_] (η (cp₀₁ g₂ y)) ∎∎

      ap-cp₁₁-coh : ∀ g₁ g₂ y →
        ap-cp₁₁-coh-seq₁ g₁ g₂ y =ₛ ap-cp₁₁-coh-seq₂ g₁ g₂ y
      ap-cp₁₁-coh g₁ g₂ y = {!!}
