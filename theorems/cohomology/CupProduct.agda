{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane
open import homotopy.EilenbergMacLane1 using (EM₁-level₁)
open import homotopy.EM1HSpaceAssoc
open import lib.types.TwoSemiCategory
open import lib.two-semi-categories.FunCategory
open import lib.two-semi-categories.FundamentalCategory

module cohomology.CupProduct {i} (R : CRing i) where

  module R = CRing R
  open R using () renaming (add-group to R₊) public

  open EM₁HSpaceAssoc R.add-ab-group hiding (comp-functor) renaming (mult to EM₁-mult) public

  module CP₀₁ (g : R.El) where

    loop' : R.El → embase' R₊ == embase
    loop' g' = emloop (R.mult g g')

    comp' : (g₁' g₂' : R.El) → loop' (R.add g₁' g₂') == loop' g₁' ∙ loop' g₂'
    comp' g₁' g₂' = ap emloop (R.distr-r g g₁' g₂') ∙ emloop-comp _ _

    module Rec = EM₁Level₁Rec {G = R₊} {C = EM₁ R₊} {{EM₁-level₁ R₊}} embase (group-hom loop' comp')

    cp₀₁ : EM₁ R₊ → EM₁ R₊
    cp₀₁ = Rec.f

  open CP₀₁ public using (cp₀₁)

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
          =⟨ CP₀₁.Rec.emloop-β g₁ h |in-ctx (λ z → ap2 (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) (ap EM₁-mult z) (emloop h)) ⟩
        ap2 (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) (ap EM₁-mult (emloop (R.mult g₁ h))) (emloop h)
          =⟨ MultRec.emloop-β (R.mult g₁ h) |in-ctx (λ z → ap2 (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) z (emloop h)) ⟩
        ap2 (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) (λ= (mult-loop (R.mult g₁ h))) (emloop h)
          =⟨ ap2-out (λ (f : EM₁ R₊ → EM₁ R₊) y → f $ cp₀₁ g₂ y) (λ= (mult-loop (R.mult g₁ h))) (emloop h) ⟩
        ap (λ (f : EM₁ R₊ → EM₁ R₊) → f embase) (λ= (mult-loop (R.mult g₁ h))) ∙ ap (cp₀₁ g₂) (emloop h)
          =⟨ app=-β (mult-loop (R.mult g₁ h)) embase |in-ctx (λ z → z ∙ ap (cp₀₁ g₂) (emloop h)) ⟩
        mult-loop (R.mult g₁ h) embase ∙ ap (cp₀₁ g₂) (emloop h)
          =⟨ idp ⟩
        emloop (R.mult g₁ h) ∙ ap (cp₀₁ g₂) (emloop h)
          =⟨ CP₀₁.Rec.emloop-β g₂ h |in-ctx (λ z → emloop (R.mult g₁ h) ∙ z) ⟩
        emloop (R.mult g₁ h) ∙ emloop (R.mult g₂ h)
          =⟨ ! (emloop-comp (R.mult g₁ h) (R.mult g₂ h)) ⟩
        emloop (R.add (R.mult g₁ h) (R.mult g₂ h))
          =⟨ ap emloop (! (R.distr-l g₁ g₂ h)) ⟩
        emloop (R.mult (R.add g₁ g₂) h)
          =⟨ ! (CP₀₁.Rec.emloop-β (R.add g₁ g₂) h) ⟩
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
        λ= (cp₀₁-distr-l (R.add g₁ g₂) g₃) ∙
        ap (λ s g' → EM₁-mult (s g') (cp₀₁ g₃ g')) (λ= (cp₀₁-distr-l g₁ g₂)) ∙
        λ= (λ g' → H-⊙EM₁-assoc (cp₀₁ g₁ g') (cp₀₁ g₂ g') (cp₀₁ g₃ g'))
        ==
        ap (λ s → cp₀₁ s) (R.add-assoc g₁ g₂ g₃) ∙
        λ= (cp₀₁-distr-l g₁ (R.add g₂ g₃)) ∙
        ap (λ s g' → EM₁-mult (cp₀₁ g₁ g') (s g')) (λ= (cp₀₁-distr-l g₂ g₃))
      pres-comp-coh g₁ g₂ g₃ =
        (λ= (cp₀₁-distr-l (R.add g₁ g₂) g₃) ◃∙
         ap (λ s g' → EM₁-mult (s g') (cp₀₁ g₃ g')) (λ= (cp₀₁-distr-l g₁ g₂)) ◃∙
         λ= (λ g' → H-⊙EM₁-assoc (cp₀₁ g₁ g') (cp₀₁ g₂ g') (cp₀₁ g₃ g')) ◃∎)
          =↯=⟨ 1 & 1 & λ= (λ g' → ap (λ s → EM₁-mult s (cp₀₁ g₃ g')) (cp₀₁-distr-l g₁ g₂ g')) ◃∎ &
               λ=-ap (λ g' s → EM₁-mult s (cp₀₁ g₃ g')) (cp₀₁-distr-l g₁ g₂) ⟩
        (λ= (cp₀₁-distr-l (R.add g₁ g₂) g₃) ◃∙
         λ= (λ g' → ap (λ s → EM₁-mult s (cp₀₁ g₃ g')) (cp₀₁-distr-l g₁ g₂ g')) ◃∙
         λ= (λ g' → H-⊙EM₁-assoc (cp₀₁ g₁ g') (cp₀₁ g₂ g') (cp₀₁ g₃ g')) ◃∎)
          =↯=⟨ 1 & 2 & λ= (λ g' → ap (λ s → EM₁-mult s (cp₀₁ g₃ g')) (cp₀₁-distr-l g₁ g₂ g') ∙
                                  H-⊙EM₁-assoc (cp₀₁ g₁ g') (cp₀₁ g₂ g') (cp₀₁ g₃ g')) ◃∎ &
               ∙-λ= (λ g' → ap (λ s → EM₁-mult s (cp₀₁ g₃ g')) (cp₀₁-distr-l g₁ g₂ g'))
                    (λ g' → H-⊙EM₁-assoc (cp₀₁ g₁ g') (cp₀₁ g₂ g') (cp₀₁ g₃ g')) ⟩
        λ= (cp₀₁-distr-l (R.add g₁ g₂) g₃) ∙
        λ= (λ g' → ap (λ s → EM₁-mult s (cp₀₁ g₃ g')) (cp₀₁-distr-l g₁ g₂ g') ∙
                    H-⊙EM₁-assoc (cp₀₁ g₁ g') (cp₀₁ g₂ g') (cp₀₁ g₃ g'))
          =⟨ ∙-λ= (cp₀₁-distr-l (R.add g₁ g₂) g₃)
                  (λ g' → ap (λ s → EM₁-mult s (cp₀₁ g₃ g')) (cp₀₁-distr-l g₁ g₂ g') ∙
                          H-⊙EM₁-assoc (cp₀₁ g₁ g') (cp₀₁ g₂ g') (cp₀₁ g₃ g')) ⟩
        λ= (cp₀₁-distr-l₁ g₁ g₂ g₃)
          =⟨ ap λ= (λ= (cp₀₁-distr-l-coh g₁ g₂ g₃)) ⟩
        λ= (cp₀₁-distr-l₂ g₁ g₂ g₃)
          =⟨ ! (∙-λ= (λ g' → ap (λ s → cp₀₁ s g') (R.add-assoc g₁ g₂ g₃))
                     (λ g' → cp₀₁-distr-l g₁ (R.add g₂ g₃) g' ∙
                             ap (EM₁-mult (cp₀₁ g₁ g')) (cp₀₁-distr-l g₂ g₃ g'))) ⟩
        (λ= (λ g' → ap (λ s → cp₀₁ s g') (R.add-assoc g₁ g₂ g₃)) ◃∙
         λ= (λ g' → cp₀₁-distr-l g₁ (R.add g₂ g₃) g' ∙
                    ap (EM₁-mult (cp₀₁ g₁ g')) (cp₀₁-distr-l g₂ g₃ g')) ◃∎)
          =↯=⟨ 1 & 1 & (λ= (cp₀₁-distr-l g₁ (R.add g₂ g₃)) ◃∙
                        λ= (λ g' → ap (EM₁-mult (cp₀₁ g₁ g')) (cp₀₁-distr-l g₂ g₃ g')) ◃∎) &
               ! (∙-λ= (cp₀₁-distr-l g₁ (R.add g₂ g₃))
                       (λ g' → ap (EM₁-mult (cp₀₁ g₁ g')) (cp₀₁-distr-l g₂ g₃ g'))) ⟩
        (λ= (λ g' → ap (λ s → cp₀₁ s g') (R.add-assoc g₁ g₂ g₃)) ◃∙
         λ= (cp₀₁-distr-l g₁ (R.add g₂ g₃)) ◃∙
         λ= (λ g' → ap (EM₁-mult (cp₀₁ g₁ g')) (cp₀₁-distr-l g₂ g₃ g')) ◃∎)
          =↯=⟨ 0 & 1 & λ= (app= (ap cp₀₁ (R.add-assoc g₁ g₂ g₃))) ◃∎ &
               ap λ= (λ= (λ g' → ap-∘ (λ f → f g') cp₀₁ (R.add-assoc g₁ g₂ g₃))) ⟩
        (λ= (app= (ap (λ s → cp₀₁ s) (R.add-assoc g₁ g₂ g₃))) ◃∙
         λ= (cp₀₁-distr-l g₁ (R.add g₂ g₃)) ◃∙
         λ= (λ g' → ap (EM₁-mult (cp₀₁ g₁ g')) (cp₀₁-distr-l g₂ g₃ g')) ◃∎)
          =↯=⟨ 0 & 1 & ap (λ s → cp₀₁ s) (R.add-assoc g₁ g₂ g₃) ◃∎ &
               ! (λ=-η (ap (λ s → cp₀₁ s) (R.add-assoc g₁ g₂ g₃))) ⟩
        (ap (λ s → cp₀₁ s) (R.add-assoc g₁ g₂ g₃) ◃∙
         λ= (cp₀₁-distr-l g₁ (R.add g₂ g₃)) ◃∙
         λ= (λ g' → ap (EM₁-mult (cp₀₁ g₁ g')) (cp₀₁-distr-l g₂ g₃ g')) ◃∎)
          =↯=⟨ 2 & 1 & ap (λ s g' → EM₁-mult (cp₀₁ g₁ g') (s g')) (λ= (cp₀₁-distr-l g₂ g₃)) ◃∎ &
               ! (λ=-ap (λ g' s → EM₁-mult (cp₀₁ g₁ g') s) (cp₀₁-distr-l g₂ g₃)) ⟩
        (ap (λ s → cp₀₁ s) (R.add-assoc g₁ g₂ g₃) ◃∙
         λ= (cp₀₁-distr-l g₁ (R.add g₂ g₃)) ◃∙
         ap (λ s g' → EM₁-mult (cp₀₁ g₁ g') (s g')) (λ= (cp₀₁-distr-l g₂ g₃)) ◃∎) ↯∎

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
    --   `EM1HSpaceAssoc.comp-functor`
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

    F : TwoSemiFunctor (group-to-cat R₊) (2-type-fundamental-cat (EM₁ R₊ → EM 2) {{C-level}})
    F =
      ab-group-cat-to-dual R.add-ab-group –F→
      dual-functor-map group-to-EM₁→EM₂-op –F→
      from-double-dual (fun-cat (EM₁ R₊) (=ₜ-fundamental-cat (Susp (EM₁ R₊)))) –F→
      fun-functor-map (EM₁ R₊) (=ₜ-to-2-type-fundamental-cat (Susp (EM₁ R₊))) –F→
      λ=-functor (EM₁ R₊) (EM 2)

    module CP₁₁-Rec = EM₁Rec {G = R₊} {C = C} {{C-level}} F

    cp₁₁ : EM₁ R₊ → EM₁ R₊ → EM 2
    cp₁₁ = CP₁₁-Rec.f

    cp₁₁-β : ∀ g → ap cp₁₁ (emloop g) == λ= (λ y → ap [_] (η (cp₀₁ g y)))
    cp₁₁-β g = CP₁₁-Rec.emloop-β g -- takes a long time to check

    app=-ap-cp₁₁ : ∀ g y → app= (ap cp₁₁ (emloop g)) y == ap [_] (η (cp₀₁ g y))
    app=-ap-cp₁₁ g y =
      ap (λ z → app= z y) (cp₁₁-β g) ∙ app=-β (λ x → ap [_] (η (cp₀₁ g x))) y
