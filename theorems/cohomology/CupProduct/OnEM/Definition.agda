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
        =⟨ =ₛ-out (ap2-out (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) (mult-loop (R.mult g₁ h)) (emloop h)) ⟩
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
        =ₛ⟨ λ=-∙∙ (λ g' → ap (λ s → cp₀₁ s g') (R.add-assoc g₁ g₂ g₃))
                  (cp₀₁-distr-l g₁ (R.add g₂ g₃))
                  (λ g' → ap (EM₁-mult (cp₀₁ g₁ g')) (cp₀₁-distr-l g₂ g₃ g')) ⟩
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
  --   `EM₁HSpaceAssoc.comp-functor R.add-ab-group`
  -- inlined but Agda chokes on this shorter definition

module _ where

  private
    T : TwoSemiCategory i i
    T = dual-cat (fun-cat (EM₁ R₊) (=ₜ-fundamental-cat (Susp (EM₁ R₊))))

    module T = TwoSemiCategory T
    cst-north : T.El
    cst-north = λ _ → [ north ]
    T-comp' = T.comp {x = cst-north} {y = cst-north} {z = cst-north}
    T-assoc' = T.assoc {x = cst-north} {y = cst-north} {z = cst-north} {w = cst-north}

  group-to-EM₁→EM₂-op : TwoSemiFunctor (group-to-cat R₊) T
  group-to-EM₁→EM₂-op =
    group-to-EM₁-endos –F→
    fun-functor-map (EM₁ R₊) comp-functor –F→
    swap-fun-dual-functor (EM₁ R₊) (=ₜ-fundamental-cat (Susp (EM₁ R₊)))

  abstract
    app=-group-to-EM₁→EM₂-op-pres-comp-embase : ∀ g₁ g₂ →
      app= (TwoSemiFunctor.pres-comp group-to-EM₁→EM₂-op g₁ g₂) embase ==
      comp embase embase
    app=-group-to-EM₁→EM₂-op-pres-comp-embase g₁ g₂ = =ₛ-out $
      app= (TwoSemiFunctor.pres-comp group-to-EM₁→EM₂-op g₁ g₂) embase ◃∎
        =ₛ⟨ ap-seq-=ₛ (λ f → f embase) (comp-functors-pres-comp-β G₀₁ G₁₃ g₁ g₂) ⟩
      app= (ap (TwoSemiFunctor.F₁ G₁₃) (TwoSemiFunctor.pres-comp G₀₁ g₁ g₂)) embase ◃∙
      app= (TwoSemiFunctor.pres-comp G₁₃ (cp₀₁ g₁) (cp₀₁ g₂)) embase ◃∎
        =ₛ⟨ 0 & 1 & =ₛ-in {t = []} $
            app= (ap (λ f x → [ η (f x) ]) (λ= (cp₀₁-distr-l g₁ g₂))) embase
              =⟨ ap (λ w → app= w embase) (λ=-ap (λ _ y → [ η y ]) (cp₀₁-distr-l g₁ g₂)) ⟩
            app= (λ= (λ a → ap (λ y → [ η y ]) (cp₀₁-distr-l g₁ g₂ a))) embase
              =⟨ app=-β (λ a → ap (λ y → [ η y ]) (cp₀₁-distr-l g₁ g₂ a)) embase ⟩
            idp =∎
          ⟩
      app= (TwoSemiFunctor.pres-comp G₁₃ (cp₀₁ g₁) (cp₀₁ g₂)) embase ◃∎
        =ₛ⟨ ap-seq-=ₛ (λ f → f embase) (comp-functors-pres-comp-β G₁₂ G₂₃ (cp₀₁ g₁) (cp₀₁ g₂)) ⟩
      app= (ap (λ f → f) (TwoSemiFunctor.pres-comp G₁₂ (cp₀₁ g₁) (cp₀₁ g₂))) embase ◃∙
      idp ◃∎
        =ₛ⟨ 1 & 1 & expand [] ⟩
      app= (ap (λ f → f) (TwoSemiFunctor.pres-comp G₁₂ (cp₀₁ g₁) (cp₀₁ g₂))) embase ◃∎
        =ₛ₁⟨ ∘-ap (λ f → f embase) (λ f → f) (TwoSemiFunctor.pres-comp G₁₂ (cp₀₁ g₁) (cp₀₁ g₂)) ⟩
      app= (λ= (λ y → comp (cp₀₁ g₁ y) (cp₀₁ g₂ y))) embase ◃∎
        =ₛ₁⟨ app=-β (λ y → comp (cp₀₁ g₁ y) (cp₀₁ g₂ y)) embase ⟩
      comp embase embase ◃∎ ∎ₛ
      where
        G₀₁ = group-to-EM₁-endos
        G₁₂ = fun-functor-map (EM₁ R₊) comp-functor
        G₂₃ = swap-fun-dual-functor (EM₁ R₊) (=ₜ-fundamental-cat (Susp (EM₁ R₊)))
        G₁₃ = G₁₂ –F→ G₂₃

module CP₁₁ where

  open EMExplicit R.add-ab-group

  private
    C : Type i
    C = EM₁ R₊ → EM 2

    C-level : has-level 2 C
    C-level = Π-level (λ _ → EM-level 2)

    D₀ : TwoSemiCategory lzero i
    D₀ = group-to-cat R₊

    D₁ : TwoSemiCategory lzero i
    D₁ = dual-cat (group-to-cat R₊)

    D₂ : TwoSemiCategory i i
    D₂ = dual-cat (dual-cat (fun-cat (EM₁ R₊) (=ₜ-fundamental-cat (Susp (EM₁ R₊)))))

    D₃' : TwoSemiCategory i i
    D₃' = =ₜ-fundamental-cat (Susp (EM₁ R₊))

    D₃ : TwoSemiCategory i i
    D₃ = fun-cat (EM₁ R₊) D₃'

    D₄' : TwoSemiCategory i i
    D₄' = 2-type-fundamental-cat (EM 2)

    D₄ : TwoSemiCategory i i
    D₄ = fun-cat (EM₁ R₊) D₄'

    D₅ : TwoSemiCategory i i
    D₅ = 2-type-fundamental-cat (EM₁ R₊ → EM 2) {{C-level}}

    F₀₁ : TwoSemiFunctor D₀ D₁
    F₀₁ = ab-group-cat-to-dual R.add-ab-group

    F₁₂ : TwoSemiFunctor D₁ D₂
    F₁₂ = dual-functor-map group-to-EM₁→EM₂-op

    F₂₃ : TwoSemiFunctor D₂ D₃
    F₂₃ = from-double-dual (fun-cat (EM₁ R₊) (=ₜ-fundamental-cat (Susp (EM₁ R₊))))

    F₃₄' : TwoSemiFunctor D₃' D₄'
    F₃₄' = =ₜ-to-2-type-fundamental-cat (Susp (EM₁ R₊))

    F₃₄ : TwoSemiFunctor D₃ D₄
    F₃₄ = fun-functor-map (EM₁ R₊) F₃₄'

    F₂₄ : TwoSemiFunctor D₂ D₄
    F₂₄ = F₂₃ –F→ F₃₄

    F₁₄ : TwoSemiFunctor D₁ D₄
    F₁₄ = F₁₂ –F→ F₂₄

  F₀₄ : TwoSemiFunctor D₀ D₄
  F₀₄ = F₀₁ –F→ F₁₄

  F₄₅ : TwoSemiFunctor D₄ D₅
  F₄₅ = λ=-functor (EM₁ R₊) (EM 2)

  module F₀₄ = TwoSemiFunctor F₀₄
  module F₄₅ = TwoSemiFunctor F₄₅

  private
    module F₀₅-Comp = FunctorComposition F₀₄ F₄₅
    F₀₅ : TwoSemiFunctor D₀ D₅
    F₀₅ = F₀₅-Comp.composition

    module F₁₂  = TwoSemiFunctor F₁₂
    module F₃₄' = TwoSemiFunctor F₃₄'
    module F₃₄  = TwoSemiFunctor F₃₄
    module F₂₄  = TwoSemiFunctor F₂₄
    module F₁₄  = TwoSemiFunctor F₁₄
    module F₀₅  = TwoSemiFunctor F₀₅

    module CP₁₁-Rec = EM₁Rec {G = R₊} {C = C} {{C-level}} F₀₅

  abstract
    cp₁₁ : EM₁ R₊ → EM₁ R₊ → EM 2
    cp₁₁ = CP₁₁-Rec.f

    cp₁₁-embase-β : cp₁₁ embase ↦ (λ _ → [ north ])
    cp₁₁-embase-β = CP₁₁-Rec.embase-β
    {-# REWRITE cp₁₁-embase-β #-}

    cp₁₁-emloop-β : ∀ g → ap cp₁₁ (emloop g) == λ= (λ y → ap [_] (η (cp₀₁ g y)))
    cp₁₁-emloop-β g = CP₁₁-Rec.emloop-β g

    app=-F₀₄-pres-comp-embase-β : ∀ g₁ g₂ →
      app= (F₀₄.pres-comp g₁ g₂) embase ◃∎
      =ₛ
      ap (ap [_]) (comp-l embase) ◃∙
      ap-∙ [_] (η embase) (η embase) ◃∎
    app=-F₀₄-pres-comp-embase-β g₁ g₂ =
      app= (F₀₄.pres-comp g₁ g₂) embase ◃∎
        =ₛ⟨ ap-seq-=ₛ (λ f → f embase) (comp-functors-pres-comp-β F₀₁ F₁₄ g₁ g₂) ⟩
      app= (ap (λ g y → ap [_] (η (cp₀₁ g y))) (R.add-comm g₁ g₂)) embase ◃∙
      app= (F₁₄.pres-comp g₁ g₂) embase ◃∎
        =ₛ⟨ 0 & 1 & =ₛ-in {t = []} $
            app= (ap (λ g y → ap [_] (η (cp₀₁ g y))) (R.add-comm g₁ g₂)) embase
              =⟨ ∘-ap (λ f → f embase) (λ g y → ap [_] (η (cp₀₁ g y))) (R.add-comm g₁ g₂) ⟩
            ap (λ g → ap [_] (η (cp₀₁ g embase))) (R.add-comm g₁ g₂)
              =⟨ ap-cst (ap [_] (η embase)) (R.add-comm g₁ g₂) ⟩
            idp
          ⟩
      app= (F₁₄.pres-comp g₁ g₂) embase ◃∎
        =ₛ⟨ ap-seq-=ₛ (λ f → f embase) (comp-functors-pres-comp-β F₁₂ F₂₄ g₁ g₂) ⟩
      app= (ap (λ α y → <– (=ₜ-equiv [ north ] [ north ]) (α y))
               (F₁₂.pres-comp g₁ g₂)) embase ◃∙
      app= (F₂₄.pres-comp {x = λ _ → [ north ]} {y = λ _ → [ north ]} {z = λ _ → [ north ]}
                          (λ y → [ η (cp₀₁ g₁ y) ]) (λ y → [ η (cp₀₁ g₂ y) ])) embase ◃∎
        =ₛ₁⟨ 0 & 1 & step₄ ⟩
      ap (ap [_]) (comp-l embase) ◃∙
      app= (F₂₄.pres-comp {x = λ _ → [ north ]} {y = λ _ → [ north ]} {z = λ _ → [ north ]}
                          (λ y → [ η (cp₀₁ g₁ y) ]) (λ y → [ η (cp₀₁ g₂ y) ])) embase ◃∎
        =ₛ⟨ 1 & 1 & ap-seq-=ₛ (λ f → f embase) $
                    comp-functors-pres-comp-β F₂₃ F₃₄
                      {x = λ _ → [ north ]} {y = λ _ → [ north ]} {z = λ _ → [ north ]}
                      (λ y → [ η (cp₀₁ g₁ y) ]₁) (λ y → [ η (cp₀₁ g₂ y) ]₁) ⟩
      ap (ap [_]) (comp-l embase) ◃∙
      idp ◃∙
      app= (F₃₄.pres-comp {x = λ _ → [ north ]} {y = λ _ → [ north ]} {z = λ _ → [ north ]}
                          (λ y → [ η (cp₀₁ g₁ y) ]₁) (λ y → [ η (cp₀₁ g₂ y) ]₁)) embase ◃∎
        =ₛ⟨ 1 & 1 & expand [] ⟩
      ap (ap [_]) (comp-l embase) ◃∙
      app= (F₃₄.pres-comp {x = λ _ → [ north ]} {y = λ _ → [ north ]} {z = λ _ → [ north ]}
                          (λ y → [ η (cp₀₁ g₁ y) ]₁) (λ y → [ η (cp₀₁ g₂ y) ]₁)) embase ◃∎
        =ₛ₁⟨ 1 & 1 & step₇ ⟩
      ap (ap [_]) (comp-l embase) ◃∙
      ap-∙ [_] (η embase) (η embase) ◃∎ ∎ₛ
      where
      step₄ :
        app= (ap (λ α y → <– (=ₜ-equiv [ north ] [ north ]) (α y))
                 (F₁₂.pres-comp g₁ g₂)) embase
        == ap (ap [_]) (comp-l embase)
      step₄ =
        app= (ap (λ α y → <– (=ₜ-equiv [ north ] [ north ]) (α y))
                 (F₁₂.pres-comp g₁ g₂)) embase
          =⟨ ∘-ap (λ f → f embase)
                  (λ α y → <– (=ₜ-equiv [ north ] [ north ]) (α y))
                  (F₁₂.pres-comp g₁ g₂) ⟩
        ap (λ α → <– (=ₜ-equiv [ north ] [ north ]) (α embase))
           (F₁₂.pres-comp g₁ g₂)
          =⟨ ap-∘ (<– (=ₜ-equiv [ north ] [ north ]))
                  (λ f → f embase)
                  (F₁₂.pres-comp g₁ g₂) ⟩
        ap (<– (=ₜ-equiv [ north ] [ north ]))
           (app= (F₁₂.pres-comp g₁ g₂) embase)
          =⟨ ap (ap (<– (=ₜ-equiv [ north ] [ north ])))
                (app=-group-to-EM₁→EM₂-op-pres-comp-embase g₂ g₁) ⟩
        ap (<– (=ₜ-equiv [ north ] [ north ])) (comp embase embase)
          =⟨ ap (ap (<– (=ₜ-equiv [ north ] [ north ])))
                (comp-unit-l embase) ⟩
        ap (<– (=ₜ-equiv [ north ] [ north ]))
           (comp-l₁ embase)
          =⟨ ∘-ap (<– (=ₜ-equiv [ north ] [ north ])) [_]₁ (comp-l embase) ⟩
        ap (ap [_]) (comp-l embase) =∎
      step₇ :
        app= (F₃₄.pres-comp {x = λ _ → [ north ]} {y = λ _ → [ north ]} {z = λ _ → [ north ]}
                            (λ y → [ η (cp₀₁ g₁ y) ]₁) (λ y → [ η (cp₀₁ g₂ y) ]₁)) embase
        == ap-∙ [_] (η embase) (η embase)
      step₇ =
        app= (F₃₄.pres-comp {x = λ _ → [ north ]} {y = λ _ → [ north ]} {z = λ _ → [ north ]}
                            (λ y → [ η (cp₀₁ g₁ y) ]₁) (λ y → [ η (cp₀₁ g₂ y) ]₁)) embase
           =⟨ app=-β (λ y → F₃₄'.pres-comp {x = [ north ]} {y = [ north ]} {z = [ north ]}
                                           [ η (cp₀₁ g₁ y) ]₁ [ η (cp₀₁ g₂ y) ]₁) embase ⟩
        F₃₄'.pres-comp {x = [ north ]} {y = [ north ]} {z = [ north ]} [ η embase ]₁ [ η embase ]₁
          =⟨ =ₜ-to-2-type-fundamental-cat-pres-comp-β (Susp (EM₁ R₊)) (η embase) (η embase) ⟩
        ap-∙ [_] (η embase) (η embase) =∎

    app=-F₀₄-pres-comp-embase-coh : ∀ g₁ g₂ →
      app= (F₀₄.pres-comp g₁ g₂) embase ◃∙
      ap2 _∙_ (ap (ap [_]) (!-inv-r (merid embase)))
              (ap (ap [_]) (!-inv-r (merid embase))) ◃∎
      =ₛ
      ap (ap [_]) (!-inv-r (merid embase)) ◃∎
    app=-F₀₄-pres-comp-embase-coh g₁ g₂ =
      app= (F₀₄.pres-comp g₁ g₂) embase ◃∙
      ap2 _∙_ (ap (ap [_]) (!-inv-r (merid embase)))
              (ap (ap [_]) (!-inv-r (merid embase))) ◃∎
        =ₛ⟨ 0 & 1 & app=-F₀₄-pres-comp-embase-β g₁ g₂ ⟩
      ap (ap [_]) (comp-l embase) ◃∙
      ap-∙ [_] (η embase) (η embase) ◃∙
      ap2 _∙_ (ap (ap [_]) (!-inv-r (merid embase)))
              (ap (ap [_]) (!-inv-r (merid embase))) ◃∎
        =ₛ₁⟨ 2 & 1 & ap2-ap-lr _∙_ (ap [_]) (ap [_]) (!-inv-r (merid embase)) (!-inv-r (merid embase)) ⟩
      ap (ap [_]) (comp-l embase) ◃∙
      ap-∙ [_] (η embase) (η embase) ◃∙
      ap2 (λ s t → ap [_] s ∙ ap [_] t) (!-inv-r (merid embase)) (!-inv-r (merid embase)) ◃∎
        =ₛ⟨ 1 & 2 & !ₛ $
            homotopy-naturality2 (λ s t → ap [_] (s ∙ t))
                                 (λ s t → ap [_] s ∙ ap [_] t)
                                 (ap-∙ [_])
                                 (!-inv-r (merid embase))
                                 (!-inv-r (merid embase)) ⟩
      ap (ap [_]) (comp-l embase) ◃∙
      ap2 (λ s t → ap [_] (s ∙ t)) (!-inv-r (merid embase)) (!-inv-r (merid embase)) ◃∙
      idp ◃∎
        =ₛ⟨ 2 & 1 & expand [] ⟩
      ap (ap [_]) (comp-l embase) ◃∙
      ap2 (λ s t → ap [_] (s ∙ t)) (!-inv-r (merid embase)) (!-inv-r (merid embase)) ◃∎
        =ₛ₁⟨ 1 & 1 & ! (ap-ap2 (ap [_]) _∙_ (!-inv-r (merid embase)) (!-inv-r (merid embase))) ⟩
      ap (ap [_]) (comp-l embase) ◃∙
      ap (ap [_]) (ap2 _∙_ (!-inv-r (merid embase)) (!-inv-r (merid embase))) ◃∎
        =ₛ⟨ ap-seq-=ₛ (ap [_]) step₇' ⟩
      ap (ap [_]) (!-inv-r (merid embase)) ◃∎ ∎ₛ
      where
        helper : ∀ {i} {A : Type i} {a₀ a₁ : A} (p : a₀ == a₁)
          → add-path-inverse-r (p ∙ ! p) p ◃∙ ap2 _∙_ (!-inv-r p) (!-inv-r p) ◃∎
            =ₛ !-inv-r p ◃∎
        helper idp = =ₛ-in idp
        step₇' : comp-l embase ◃∙ ap2 _∙_ (!-inv-r (merid embase)) (!-inv-r (merid embase)) ◃∎
                =ₛ !-inv-r (merid embase) ◃∎
        step₇' = helper (merid embase)

    app=-ap-cp₁₁-seq : ∀ g y → app= (ap cp₁₁ (emloop g)) y =-= ap [_] (η (cp₀₁ g y))
    app=-ap-cp₁₁-seq g y =
      app= (ap cp₁₁ (emloop g)) y
        =⟪ ap (λ p → app= p y) (cp₁₁-emloop-β g) ⟫
      app= (λ= (λ x → ap [_] (η (cp₀₁ g x)))) y
        =⟪ app=-β (λ x → ap [_] (η (cp₀₁ g x))) y ⟫
      ap [_] (η (cp₀₁ g y)) ∎∎

    app=-ap-cp₁₁ : ∀ g y → app= (ap cp₁₁ (emloop g)) y == ap [_] (η (cp₀₁ g y))
    app=-ap-cp₁₁ g y = ↯ (app=-ap-cp₁₁-seq g y)

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
      =⟪ app= (F₀₄.pres-comp g₁ g₂) y ⟫
    ap [_] (η (cp₀₁ g₁ y)) ∙ ap [_] (η (cp₀₁ g₂ y)) ∎∎

  abstract
    app=-ap-cp₁₁-coh : ∀ g₁ g₂ y →
      app=-ap-cp₁₁-coh-seq₁ g₁ g₂ y =ₛ app=-ap-cp₁₁-coh-seq₂ g₁ g₂ y
    app=-ap-cp₁₁-coh g₁ g₂ y =
      ap (λ u → app= (ap cp₁₁ u) y) (emloop-comp g₁ g₂) ◃∙
      ap (λ u → app= u y) (ap-∙ cp₁₁ (emloop g₁) (emloop g₂)) ◃∙
      ap-∙ (λ f → f y) (ap cp₁₁ (emloop g₁)) (ap cp₁₁ (emloop g₂)) ◃∙
      ap2 _∙_ (app=-ap-cp₁₁ g₁ y) (app=-ap-cp₁₁ g₂ y) ◃∎
        =ₛ⟨ 3 & 2 & ap2-seq-∙ _∙_ (app=-ap-cp₁₁-seq g₁ y) (app=-ap-cp₁₁-seq g₂ y) ⟩
      ap (λ u → app= (ap cp₁₁ u) y) (emloop-comp g₁ g₂) ◃∙
      ap (λ u → app= u y) (ap-∙ cp₁₁ (emloop g₁) (emloop g₂)) ◃∙
      ap-∙ (λ f → f y) (ap cp₁₁ (emloop g₁)) (ap cp₁₁ (emloop g₂)) ◃∙
      ap2 _∙_ (ap (λ z → app= z y) (cp₁₁-emloop-β g₁)) (ap (λ z → app= z y) (cp₁₁-emloop-β g₂)) ◃∙
      ap2 _∙_ (app=-β (λ x → ap [_] (η (cp₀₁ g₁ x))) y) (app=-β (λ x → ap [_] (η (cp₀₁ g₂ x))) y) ◃∎
        =ₛ₁⟨ 3 & 1 & ap2-ap-lr _∙_ (λ z → app= z y) (λ z → app= z y) (cp₁₁-emloop-β g₁) (cp₁₁-emloop-β g₂) ⟩
      ap (λ u → app= (ap cp₁₁ u) y) (emloop-comp g₁ g₂) ◃∙
      ap (λ u → app= u y) (ap-∙ cp₁₁ (emloop g₁) (emloop g₂)) ◃∙
      ap-∙ (λ f → f y) (ap cp₁₁ (emloop g₁)) (ap cp₁₁ (emloop g₂)) ◃∙
      ap2 (λ a b → app= a y ∙ app= b y) (cp₁₁-emloop-β g₁) (cp₁₁-emloop-β g₂) ◃∙
      ap2 _∙_ (app=-β (λ x → ap [_] (η (cp₀₁ g₁ x))) y) (app=-β (λ x → ap [_] (η (cp₀₁ g₂ x))) y) ◃∎
        =ₛ⟨ 2 & 2 & !ₛ $
            homotopy-naturality2 (λ a b → app= (a ∙ b) y)
                                  (λ a b → app= a y ∙ app= b y)
                                  (ap-∙ (λ f → f y))
                                  (cp₁₁-emloop-β g₁) (cp₁₁-emloop-β g₂) ⟩
      ap (λ u → app= (ap cp₁₁ u) y) (emloop-comp g₁ g₂) ◃∙
      ap (λ u → app= u y) (ap-∙ cp₁₁ (emloop g₁) (emloop g₂)) ◃∙
      ap2 (λ a b → app= (a ∙ b) y) (cp₁₁-emloop-β g₁) (cp₁₁-emloop-β g₂) ◃∙
      ap-∙ (λ f → f y) (λ= (λ y' → ap [_] (η (cp₀₁ g₁ y')))) (λ= (λ y' → ap [_] (η (cp₀₁ g₂ y')))) ◃∙
      ap2 _∙_ (app=-β (λ x → ap [_] (η (cp₀₁ g₁ x))) y) (app=-β (λ x → ap [_] (η (cp₀₁ g₂ x))) y) ◃∎
        =ₛ⟨ 3 & 2 &
            app=-β-coh (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x))) y ⟩
      ap (λ x → app= (ap cp₁₁ x) y) (emloop-comp g₁ g₂) ◃∙
      ap (λ p → app= p y) (ap-∙ cp₁₁ (emloop g₁) (emloop g₂)) ◃∙
      ap2 (λ a b → app= (a ∙ b) y) (cp₁₁-emloop-β g₁) (cp₁₁-emloop-β g₂) ◃∙
      ap (λ p → app= p y) (=ₛ-out (∙-λ= (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x))))) ◃∙
      app=-β (λ x → ap [_] (η (cp₀₁ g₁ x)) ∙ ap [_] (η (cp₀₁ g₂ x))) y ◃∎
        =ₛ₁⟨ 0 & 1 & ap-∘ (λ p → app= p y) (ap cp₁₁) (emloop-comp g₁ g₂) ⟩
      ap (λ p → app= p y) (ap (ap cp₁₁) (emloop-comp g₁ g₂)) ◃∙
      ap (λ p → app= p y) (ap-∙ cp₁₁ (emloop g₁) (emloop g₂)) ◃∙
      ap2 (λ a b → app= (a ∙ b) y) (cp₁₁-emloop-β g₁) (cp₁₁-emloop-β g₂) ◃∙
      ap (λ p → app= p y) (=ₛ-out (∙-λ= (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x))))) ◃∙
      app=-β (λ x → ap [_] (η (cp₀₁ g₁ x)) ∙ ap [_] (η (cp₀₁ g₂ x))) y ◃∎
        =ₛ₁⟨ 2 & 1 & ! (ap-ap2 (λ p → app= p y) _∙_ (cp₁₁-emloop-β g₁) (cp₁₁-emloop-β g₂)) ⟩
      ap (λ p → app= p y) (ap (ap cp₁₁) (emloop-comp g₁ g₂)) ◃∙
      ap (λ p → app= p y) (ap-∙ cp₁₁ (emloop g₁) (emloop g₂)) ◃∙
      ap (λ p → app= p y) (ap2 _∙_ (cp₁₁-emloop-β g₁) (cp₁₁-emloop-β g₂)) ◃∙
      ap (λ p → app= p y) (=ₛ-out (∙-λ= (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x))))) ◃∙
      app=-β (λ x → ap [_] (η (cp₀₁ g₁ x)) ∙ ap [_] (η (cp₀₁ g₂ x))) y ◃∎
        =ₛ⟨ 0 & 3 & ap-seq-=ₛ (λ p → app= p y) (CP₁₁-Rec.emloop-comp-path g₁ g₂) ⟩
      ap (λ p → app= p y) (cp₁₁-emloop-β (R.add g₁ g₂)) ◃∙
      ap (λ p → app= p y) (F₀₅.pres-comp g₁ g₂) ◃∙
      ap (λ p → app= p y) (=ₛ-out (∙-λ= (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x))))) ◃∙
      app=-β (λ x → ap [_] (η (cp₀₁ g₁ x)) ∙ ap [_] (η (cp₀₁ g₂ x))) y ◃∎
        =ₛ⟨ 1 & 2 & step₈ ⟩
      ap (λ p → app= p y) (cp₁₁-emloop-β (R.add g₁ g₂)) ◃∙
      ap (λ p → app= p y) (ap λ= (F₀₄.pres-comp g₁ g₂)) ◃∙
      app=-β (λ x → ap [_] (η (cp₀₁ g₁ x)) ∙ ap [_] (η (cp₀₁ g₂ x))) y ◃∎
        =ₛ₁⟨ 1 & 1 & ∘-ap (λ p → app= p y) λ= (F₀₄.pres-comp g₁ g₂) ⟩
      ap (λ p → app= p y) (cp₁₁-emloop-β (R.add g₁ g₂)) ◃∙
      ap (λ γ → app= (λ= γ) y) (F₀₄.pres-comp g₁ g₂) ◃∙
      app=-β (λ x → ap [_] (η (cp₀₁ g₁ x)) ∙ ap [_] (η (cp₀₁ g₂ x))) y ◃∎
        =ₛ⟨ 1 & 2 &
            homotopy-naturality (λ γ → app= (λ= γ) y)
                                (λ γ → γ y)
                                (λ γ → app=-β γ y)
                                (F₀₄.pres-comp g₁ g₂) ⟩
      ap (λ p → app= p y) (cp₁₁-emloop-β (R.add g₁ g₂)) ◃∙
      app=-β (λ x → ap [_] (η (cp₀₁ (R.add g₁ g₂) x))) y ◃∙
      app= (F₀₄.pres-comp g₁ g₂) y ◃∎
        =ₛ⟨ 0 & 2 & contract ⟩
      app=-ap-cp₁₁ (R.add g₁ g₂) y ◃∙
      app= (F₀₄.pres-comp g₁ g₂) y ◃∎ ∎ₛ
      where
      step₈ :
        ap (λ p → app= p y) (F₀₅.pres-comp g₁ g₂) ◃∙
        ap (λ p → app= p y) (=ₛ-out (∙-λ= (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x))))) ◃∎
        =ₛ
        ap (λ p → app= p y) (ap λ= (F₀₄.pres-comp g₁ g₂)) ◃∎
      step₈ = ap-seq-=ₛ (λ p → app= p y) $
        F₀₅.pres-comp g₁ g₂ ◃∙
        =ₛ-out (∙-λ= (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x)))) ◃∎
          =ₛ⟨ 0 & 1 & F₀₅-Comp.pres-comp-β g₁ g₂ ⟩
        ap λ= (F₀₄.pres-comp g₁ g₂) ◃∙
        F₄₅.pres-comp (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x))) ◃∙
        =ₛ-out (∙-λ= (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x)))) ◃∎
          =ₛ₁⟨ 1 & 1 & λ=-functor-pres-comp=λ=-∙ (EM₁ R₊) (EM 2) (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x))) ⟩
        ap λ= (F₀₄.pres-comp g₁ g₂) ◃∙
        =ₛ-out (λ=-∙ (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x)))) ◃∙
        =ₛ-out (∙-λ= (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x)))) ◃∎
          =ₛ⟨ 1 & 2 & seq-!-inv-l (=ₛ-out (∙-λ= (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x)))) ◃∎) ⟩
        ap λ= (F₀₄.pres-comp g₁ g₂) ◃∎ ∎ₛ

    ap-cp₁₁-seq : ∀ g y → ap (λ x → cp₁₁ x y) (emloop g) =-= ap [_] (η (cp₀₁ g y))
    ap-cp₁₁-seq g y =
      ap (λ x → cp₁₁ x y) (emloop g)
        =⟪ ap-∘ (λ f → f y) cp₁₁ (emloop g) ⟫
      ap (λ f → f y) (ap cp₁₁ (emloop g))
        =⟪ app=-ap-cp₁₁ g y ⟫
      ap [_] (η (cp₀₁ g y)) ∎∎

    ap-cp₁₁ : ∀ g y → ap (λ x → cp₁₁ x y) (emloop g) == ap [_] (η (cp₀₁ g y))
    ap-cp₁₁ g y = ↯ (ap-cp₁₁-seq g y)

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
      =⟪ app= (F₀₄.pres-comp g₁ g₂) y ⟫
    ap [_] (η (cp₀₁ g₁ y)) ∙ ap [_] (η (cp₀₁ g₂ y)) ∎∎

  abstract
    ap-cp₁₁-coh : ∀ g₁ g₂ y →
      ap-cp₁₁-coh-seq₁ g₁ g₂ y =ₛ ap-cp₁₁-coh-seq₂ g₁ g₂ y
    ap-cp₁₁-coh g₁ g₂ y =
      ap (ap (λ x → cp₁₁ x y)) (emloop-comp g₁ g₂) ◃∙
      ap-∙ (λ x → cp₁₁ x y) (emloop g₁) (emloop g₂) ◃∙
      ap2 _∙_ (ap-cp₁₁ g₁ y) (ap-cp₁₁ g₂ y) ◃∎
        =ₛ⟨ 2 & 1 & ap2-seq-∙ _∙_ (ap-cp₁₁-seq g₁ y) (ap-cp₁₁-seq g₂ y) ⟩
      ap (ap (λ x → cp₁₁ x y)) (emloop-comp g₁ g₂) ◃∙
      ap-∙ (λ x → cp₁₁ x y) (emloop g₁) (emloop g₂) ◃∙
      ap2 _∙_ (ap-∘ (λ f → f y) cp₁₁ (emloop g₁)) (ap-∘ (λ f → f y) cp₁₁ (emloop g₂)) ◃∙
      ap2 _∙_ (app=-ap-cp₁₁ g₁ y) (app=-ap-cp₁₁ g₂ y) ◃∎
        =ₛ⟨ 1 & 2 & ap-∘-∙-coh (λ f → f y) cp₁₁ (emloop g₁) (emloop g₂) ⟩
      ap (ap (λ x → cp₁₁ x y)) (emloop-comp g₁ g₂) ◃∙
      ap-∘ (λ f → f y) cp₁₁ (emloop g₁ ∙ emloop g₂) ◃∙
      ap (ap (λ f → f y)) (ap-∙ cp₁₁ (emloop g₁) (emloop g₂)) ◃∙
      ap-∙ (λ f → f y) (ap cp₁₁ (emloop g₁)) (ap cp₁₁ (emloop g₂)) ◃∙
      ap2 _∙_ (app=-ap-cp₁₁ g₁ y) (app=-ap-cp₁₁ g₂ y) ◃∎
        =ₛ⟨ 0 & 2 & homotopy-naturality {A = embase' R₊ == embase} {B = cp₁₁ embase y == cp₁₁ embase y}
                                        (ap (λ x → cp₁₁ x y)) (λ p → app= (ap cp₁₁ p) y)
                                        (ap-∘ (λ f → f y) cp₁₁) (emloop-comp g₁ g₂) ⟩
      ap-∘ (λ f → f y) cp₁₁ (emloop (R.add g₁ g₂)) ◃∙
      ap (λ p → app= (ap cp₁₁ p) y) (emloop-comp g₁ g₂) ◃∙
      ap (ap (λ f → f y)) (ap-∙ cp₁₁ (emloop g₁) (emloop g₂)) ◃∙
      ap-∙ (λ f → f y) (ap cp₁₁ (emloop g₁)) (ap cp₁₁ (emloop g₂)) ◃∙
      ap2 _∙_ (app=-ap-cp₁₁ g₁ y) (app=-ap-cp₁₁ g₂ y) ◃∎
        =ₛ⟨ 1 & 4 & app=-ap-cp₁₁-coh g₁ g₂ y ⟩
      ap-∘ (λ f → f y) cp₁₁ (emloop (R.add g₁ g₂)) ◃∙
      app=-ap-cp₁₁ (R.add g₁ g₂) y ◃∙
      app= (F₀₄.pres-comp g₁ g₂) y ◃∎
        =ₛ₁⟨ 0 & 2 & idp ⟩
      ap-cp₁₁ (R.add g₁ g₂) y ◃∙
      app= (F₀₄.pres-comp g₁ g₂) y ◃∎ ∎ₛ

  ap-cp₁₁-embase-seq : ∀ g →
    ap (λ x → cp₁₁ x embase) (emloop g) =-= idp
  ap-cp₁₁-embase-seq g =
    ap (λ x → cp₁₁ x embase) (emloop g)
      =⟪ ap-cp₁₁ g embase ⟫
    ap [_] (η (cp₀₁ g embase))
      =⟪idp⟫
    ap [_] (η embase)
      =⟪ ap (ap [_]) (!-inv-r (merid embase)) ⟫
    ap [_] (idp {a = north})
      =⟪idp⟫
    idp ∎∎

  ap-cp₁₁-embase : ∀ g →
    ap (λ x → cp₁₁ x embase) (emloop g) == idp
  ap-cp₁₁-embase g = ↯ (ap-cp₁₁-embase-seq g)

  ap-cp₁₁-embase-coh-seq : ∀ g₁ g₂ →
    ap (λ x → cp₁₁ x embase) (emloop (R.add g₁ g₂)) =-= idp
  ap-cp₁₁-embase-coh-seq g₁ g₂ =
    ap (λ x → cp₁₁ x embase) (emloop (R.add g₁ g₂))
      =⟪ ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ⟫
    ap (λ x → cp₁₁ x embase) (emloop g₁ ∙ emloop g₂)
      =⟪ ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂) ⟫
    ap (λ x → cp₁₁ x embase) (emloop g₁) ∙ ap (λ x → cp₁₁ x embase) (emloop g₂)
      =⟪ ap2 _∙_ (ap-cp₁₁-embase g₁) (ap-cp₁₁-embase g₂) ⟫
    idp ∎∎

  ap-cp₁₁-embase-coh : ∀ g₁ g₂ →
    ap-cp₁₁-embase (R.add g₁ g₂) ◃∎ =ₛ ap-cp₁₁-embase-coh-seq g₁ g₂
  ap-cp₁₁-embase-coh g₁ g₂ =
    ap-cp₁₁-embase (R.add g₁ g₂) ◃∎
      =ₛ⟨ expand (ap-cp₁₁-embase-seq (R.add g₁ g₂)) ⟩
    ap-cp₁₁ (R.add g₁ g₂) embase ◃∙
    ap (ap [_]) (!-inv-r (merid embase)) ◃∎
      =ₛ⟨ 1 & 1 & !ₛ (app=-F₀₄-pres-comp-embase-coh g₁ g₂) ⟩
    ap-cp₁₁ (R.add g₁ g₂) embase ◃∙
    app= (F₀₄.pres-comp g₁ g₂) embase ◃∙
    ap2 _∙_ (ap (ap [_]) (!-inv-r (merid embase))) (ap (ap [_]) (!-inv-r (merid embase))) ◃∎
      =ₛ⟨ 0 & 2 & !ₛ (ap-cp₁₁-coh g₁ g₂ embase) ⟩
    ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ◃∙
    ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂) ◃∙
    ap2 _∙_ (ap-cp₁₁ g₁ embase) (ap-cp₁₁ g₂ embase) ◃∙
    ap2 _∙_ (ap (ap [_]) (!-inv-r (merid embase))) (ap (ap [_]) (!-inv-r (merid embase))) ◃∎
      =ₛ⟨ 2 & 2 & ∙-ap2-seq _∙_ (ap-cp₁₁-embase-seq g₁) (ap-cp₁₁-embase-seq g₂) ⟩
    ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ◃∙
    ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂) ◃∙
    ap2 _∙_ (ap-cp₁₁-embase g₁) (ap-cp₁₁-embase g₂) ◃∎ ∎ₛ
