{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane
open import homotopy.EilenbergMacLane1
open import homotopy.EilenbergMacLaneFunctor
open import homotopy.EM1HSpaceAssoc
open import lib.types.TwoSemiCategory
open import lib.two-semi-categories.FunCategory
open import lib.two-semi-categories.FundamentalCategory

module cohomology.CupProduct.OnEM.InLowDegrees {i} {j} (G : AbGroup i) (H : AbGroup j) where

private
  module G = AbGroup G
  module H = AbGroup H
  module G⊗H = TensorProduct G H
  open G⊗H using (_⊗_)
  open EMExplicit

∧-cp₀₀' : G.⊙El ∧ H.⊙El → G⊗H.El
∧-cp₀₀' =
  Smash-rec
    G⊗H._⊗_
    G⊗H.ident
    G⊗H.ident
    G⊗H.⊗-ident-r
    G⊗H.⊗-ident-l

⊙∧-cp₀₀' : G.⊙El ⊙∧ H.⊙El ⊙→ G⊗H.⊙El
⊙∧-cp₀₀' = ∧-cp₀₀' , G⊗H.⊗-ident-l H.ident

⊙∧-cp₀₀-seq : (⊙EM G 0 ⊙∧ ⊙EM H 0) ⊙–→ ⊙EM G⊗H.abgroup 0
⊙∧-cp₀₀-seq =
  ⊙–> (⊙emloop-equiv G⊗H.grp) ◃⊙∘
  ⊙∧-cp₀₀' ◃⊙∘
  ⊙∧-fmap (⊙<– (⊙emloop-equiv G.grp)) (⊙<– (⊙emloop-equiv H.grp)) ◃⊙idf

⊙∧-cp₀₀ : ⊙EM G 0 ⊙∧ ⊙EM H 0 ⊙→ ⊙EM G⊗H.abgroup 0
⊙∧-cp₀₀ = ⊙compose ⊙∧-cp₀₀-seq

∧-cp₀₀ : ⊙EM G 0 ∧ ⊙EM H 0 → EM G⊗H.abgroup 0
∧-cp₀₀ = fst ⊙∧-cp₀₀

open EM₁HSpaceAssoc G⊗H.abgroup hiding (comp-functor) renaming (mult to EM₁-mult) public

cp₀₁ : G.El → EM₁ H.grp → EM₁ G⊗H.grp
cp₀₁ g = EM₁-fmap (G⊗H.ins-r-hom g)

abstract
  cp₀₁-emloop-β : ∀ g h → ap (cp₀₁ g) (emloop h) == emloop (g ⊗ h)
  cp₀₁-emloop-β g = EM₁-fmap-emloop-β (G⊗H.ins-r-hom g)

cp₀₁-distr-l : (g₁ g₂ : G.El) (y : EM₁ H.grp)
  → cp₀₁ (G.comp g₁ g₂) y == EM₁-mult (cp₀₁ g₁ y) (cp₀₁ g₂ y)
cp₀₁-distr-l g₁ g₂ =
  EM₁-set-elim
    {P = λ x → f x == g x}
    {{λ x → has-level-apply (EM₁-level₁ G⊗H.grp) _ _}}
    idp loop'
  where
  f : EM₁ H.grp → EM₁ G⊗H.grp
  f x = cp₀₁ (G.comp g₁ g₂) x
  g : EM₁ H.grp → EM₁ G⊗H.grp
  g x = EM₁-mult (cp₀₁ g₁ x) (cp₀₁ g₂ x)
  abstract
    loop' : (h : H.El) → idp == idp [ (λ x → f x == g x) ↓ emloop h ]
    loop' h = ↓-='-in {f = f} {g = g} {p = emloop h} {u = idp} {v = idp} $
      idp ∙' ap g (emloop h)
        =⟨ ∙'-unit-l (ap g (emloop h)) ⟩
      ap g (emloop h)
        =⟨ ! (ap2-diag (λ x y → EM₁-mult (cp₀₁ g₁ x) (cp₀₁ g₂ y)) (emloop h)) ⟩
      ap2 (λ x y → EM₁-mult (cp₀₁ g₁ x) (cp₀₁ g₂ y)) (emloop h) (emloop h)
        =⟨ =ₛ-out $ ap2-out (λ x y → EM₁-mult (cp₀₁ g₁ x) (cp₀₁ g₂ y)) (emloop h) (emloop h) ⟩
      ap (λ x → EM₁-mult (cp₀₁ g₁ x) embase) (emloop h) ∙ ap (cp₀₁ g₂) (emloop h)
        =⟨ ap2 _∙_ part (cp₀₁-emloop-β g₂ h) ⟩
      emloop (g₁ ⊗ h) ∙ emloop (g₂ ⊗ h)
        =⟨ ! (emloop-comp (g₁ ⊗ h) (g₂ ⊗ h)) ⟩
      emloop (G⊗H.comp (g₁ ⊗ h) (g₂ ⊗ h))
        =⟨ ap emloop (! (G⊗H.⊗-lin-l g₁ g₂ h)) ⟩
      emloop (G.comp g₁ g₂ ⊗ h)
        =⟨ ! (cp₀₁-emloop-β (G.comp g₁ g₂) h) ⟩
      ap f (emloop h)
        =⟨ ! (∙-unit-r (ap f (emloop h))) ⟩
      ap f (emloop h) ∙ idp =∎
      where
      part : ap (λ x → EM₁-mult (cp₀₁ g₁ x) embase) (emloop h) == emloop (g₁ ⊗ h)
      part =
        ap (λ x → EM₁-mult (cp₀₁ g₁ x) embase) (emloop h)
          =⟨ ap-∘ (λ u → EM₁-mult u embase) (cp₀₁ g₁) (emloop h) ⟩
        ap (λ u → EM₁-mult u embase) (ap (cp₀₁ g₁) (emloop h))
          =⟨ ap (ap (λ u → EM₁-mult u embase)) (cp₀₁-emloop-β g₁ h) ⟩
        ap (λ u → EM₁-mult u embase) (emloop (g₁ ⊗ h))
          =⟨ mult-emloop-β (g₁ ⊗ h) embase ⟩
        emloop (g₁ ⊗ h) =∎

module _ (g₁ g₂ g₃ : G.El) (y : EM₁ H.grp) where

  cp₀₁-distr-l₁ : cp₀₁ (G.comp (G.comp g₁ g₂) g₃) y =-=
                  EM₁-mult (cp₀₁ g₁ y) (EM₁-mult (cp₀₁ g₂ y) (cp₀₁ g₃ y))
  cp₀₁-distr-l₁ =
    cp₀₁ (G.comp (G.comp g₁ g₂) g₃) y
      =⟪ cp₀₁-distr-l (G.comp g₁ g₂) g₃ y ⟫
    EM₁-mult (cp₀₁ (G.comp g₁ g₂) y) (cp₀₁ g₃ y)
      =⟪ ap (λ s → EM₁-mult s (cp₀₁ g₃ y)) (cp₀₁-distr-l g₁ g₂ y) ⟫
    EM₁-mult (EM₁-mult (cp₀₁ g₁ y) (cp₀₁ g₂ y)) (cp₀₁ g₃ y)
      =⟪ H-⊙EM₁-assoc (cp₀₁ g₁ y) (cp₀₁ g₂ y) (cp₀₁ g₃ y) ⟫
    EM₁-mult (cp₀₁ g₁ y) (EM₁-mult (cp₀₁ g₂ y) (cp₀₁ g₃ y)) ∎∎

  cp₀₁-distr-l₂ : cp₀₁ (G.comp (G.comp g₁ g₂) g₃) y =-=
                  EM₁-mult (cp₀₁ g₁ y) (EM₁-mult (cp₀₁ g₂ y) (cp₀₁ g₃ y))
  cp₀₁-distr-l₂ =
    cp₀₁ (G.comp (G.comp g₁ g₂) g₃) y
      =⟪ ap (λ s → cp₀₁ s y) (G.assoc g₁ g₂ g₃) ⟫
    cp₀₁ (G.comp g₁ (G.comp g₂ g₃)) y
      =⟪ cp₀₁-distr-l g₁ (G.comp g₂ g₃) y ⟫
    EM₁-mult (cp₀₁ g₁ y) (cp₀₁ (G.comp g₂ g₃) y)
      =⟪ ap (EM₁-mult (cp₀₁ g₁ y)) (cp₀₁-distr-l g₂ g₃ y) ⟫
    EM₁-mult (cp₀₁ g₁ y) (EM₁-mult (cp₀₁ g₂ y) (cp₀₁ g₃ y)) ∎∎

abstract
  cp₀₁-distr-l-coh : (g₁ g₂ g₃ : G.El) (y : EM₁ H.grp)
    → cp₀₁-distr-l₁ g₁ g₂ g₃ y =ₛ cp₀₁-distr-l₂ g₁ g₂ g₃ y
  cp₀₁-distr-l-coh g₁ g₂ g₃ =
    EM₁-prop-elim
      {P = λ y → cp₀₁-distr-l₁ g₁ g₂ g₃ y =ₛ cp₀₁-distr-l₂ g₁ g₂ g₃ y}
      {{λ y → =ₛ-level (EM₁-level₁ G⊗H.grp)}} $
    idp ◃∙ idp ◃∙ idp ◃∎
      =ₛ₁⟨ 0 & 1 & ! (ap-cst embase (G.assoc g₁ g₂ g₃)) ⟩
    ap (cst embase) (G.assoc g₁ g₂ g₃) ◃∙ idp ◃∙ idp ◃∎ ∎ₛ

group-to-EM₁H→EM₁G⊗H :
  TwoSemiFunctor
    (group-to-cat G.grp)
    (fun-cat (EM₁ H.grp) EM₁-2-semi-category)
group-to-EM₁H→EM₁G⊗H =
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
      λ= (cp₀₁-distr-l (G.comp g₁ g₂) g₃) ◃∙
      ap (λ s y → EM₁-mult (s y) (cp₀₁ g₃ y)) (λ= (cp₀₁-distr-l g₁ g₂)) ◃∙
      λ= (λ y → H-⊙EM₁-assoc (cp₀₁ g₁ y) (cp₀₁ g₂ y) (cp₀₁ g₃ y)) ◃∎
      =ₛ
      ap (λ s → cp₀₁ s) (G.assoc g₁ g₂ g₃) ◃∙
      λ= (cp₀₁-distr-l g₁ (G.comp g₂ g₃)) ◃∙
      ap (λ s y → EM₁-mult (cp₀₁ g₁ y) (s y)) (λ= (cp₀₁-distr-l g₂ g₃)) ◃∎
    pres-comp-coh g₁ g₂ g₃ =
      λ= (cp₀₁-distr-l (G.comp g₁ g₂) g₃) ◃∙
      ap (λ s y → EM₁-mult (s y) (cp₀₁ g₃ y)) (λ= (cp₀₁-distr-l g₁ g₂)) ◃∙
      λ= (λ y → H-⊙EM₁-assoc (cp₀₁ g₁ y) (cp₀₁ g₂ y) (cp₀₁ g₃ y)) ◃∎
        =ₛ₁⟨ 1 & 1 & λ=-ap (λ y s → EM₁-mult s (cp₀₁ g₃ y)) (cp₀₁-distr-l g₁ g₂) ⟩
      λ= (cp₀₁-distr-l (G.comp g₁ g₂) g₃) ◃∙
      λ= (λ y → ap (λ s → EM₁-mult s (cp₀₁ g₃ y)) (cp₀₁-distr-l g₁ g₂ y)) ◃∙
      λ= (λ y → H-⊙EM₁-assoc (cp₀₁ g₁ y) (cp₀₁ g₂ y) (cp₀₁ g₃ y)) ◃∎
        =ₛ⟨ ∙∙-λ= (cp₀₁-distr-l (G.comp g₁ g₂) g₃)
                  (λ y → ap (λ s → EM₁-mult s (cp₀₁ g₃ y)) (cp₀₁-distr-l g₁ g₂ y))
                  (λ y → H-⊙EM₁-assoc (cp₀₁ g₁ y) (cp₀₁ g₂ y) (cp₀₁ g₃ y)) ⟩
      λ= (λ y → ↯ (cp₀₁-distr-l₁ g₁ g₂ g₃ y)) ◃∎
        =ₛ₁⟨ ap λ= (λ= (λ y → =ₛ-out (cp₀₁-distr-l-coh g₁ g₂ g₃ y))) ⟩
      λ= (λ y → ↯ (cp₀₁-distr-l₂ g₁ g₂ g₃ y)) ◃∎
        =ₛ⟨ λ=-∙∙ (λ y → ap (λ s → cp₀₁ s y) (G.assoc g₁ g₂ g₃))
                  (cp₀₁-distr-l g₁ (G.comp g₂ g₃))
                  (λ y → ap (EM₁-mult (cp₀₁ g₁ y)) (cp₀₁-distr-l g₂ g₃ y)) ⟩
      λ= (λ y → ap (λ s → cp₀₁ s y) (G.assoc g₁ g₂ g₃)) ◃∙
      λ= (cp₀₁-distr-l g₁ (G.comp g₂ g₃)) ◃∙
      λ= (λ y → ap (EM₁-mult (cp₀₁ g₁ y)) (cp₀₁-distr-l g₂ g₃ y)) ◃∎
        =ₛ₁⟨ 0 & 1 & ap λ= (λ= (λ y → ap-∘ (λ f → f y) cp₀₁ (G.assoc g₁ g₂ g₃))) ⟩
      λ= (app= (ap (λ s → cp₀₁ s) (G.assoc g₁ g₂ g₃))) ◃∙
      λ= (cp₀₁-distr-l g₁ (G.comp g₂ g₃)) ◃∙
      λ= (λ y → ap (EM₁-mult (cp₀₁ g₁ y)) (cp₀₁-distr-l g₂ g₃ y)) ◃∎
        =ₛ₁⟨ 0 & 1 & ! (λ=-η (ap (λ s → cp₀₁ s) (G.assoc g₁ g₂ g₃))) ⟩
      ap (λ s → cp₀₁ s) (G.assoc g₁ g₂ g₃) ◃∙
      λ= (cp₀₁-distr-l g₁ (G.comp g₂ g₃)) ◃∙
      λ= (λ y → ap (EM₁-mult (cp₀₁ g₁ y)) (cp₀₁-distr-l g₂ g₃ y)) ◃∎
        =ₛ₁⟨ 2 & 1 & ! (λ=-ap (λ y s → EM₁-mult (cp₀₁ g₁ y) s) (cp₀₁-distr-l g₂ g₃)) ⟩
      ap (λ s → cp₀₁ s) (G.assoc g₁ g₂ g₃) ◃∙
      λ= (cp₀₁-distr-l g₁ (G.comp g₂ g₃)) ◃∙
      ap (λ s y → EM₁-mult (cp₀₁ g₁ y) (s y)) (λ= (cp₀₁-distr-l g₂ g₃)) ◃∎ ∎ₛ

comp-functor :
  TwoSemiFunctor
    EM₁-2-semi-category
    (=ₜ-fundamental-cat (Susp (EM₁ G⊗H.grp)))
comp-functor =
  record
  { F₀ = λ _ → [ north ]
  ; F₁ = λ x → [ η x ]
  ; pres-comp = comp
  ; pres-comp-coh = comp-coh
  }
  -- this is *exactly* the same as
  --   `EM₁HSpaceAssoc.comp-functor G⊗H.abgroup`
  -- inlined but Agda chokes on this shorter definition

module _ where

  private
    T : TwoSemiCategory (lmax i j) (lmax i j)
    T = fun-cat (EM₁ H.grp) (=ₜ-fundamental-cat (Susp (EM₁ G⊗H.grp)))

    module T = TwoSemiCategory T
    cst-north : T.El
    cst-north = λ _ → [ north ]
    T-comp' = T.comp {x = cst-north} {y = cst-north} {z = cst-north}
    T-assoc' = T.assoc {x = cst-north} {y = cst-north} {z = cst-north} {w = cst-north}

  group-to-EM₁→EM₂-op : TwoSemiFunctor (group-to-cat G.grp) T
  group-to-EM₁→EM₂-op =
    group-to-EM₁H→EM₁G⊗H –F→
    fun-functor-map (EM₁ H.grp) comp-functor

  abstract
    app=-group-to-EM₁→EM₂-op-pres-comp-embase : ∀ g₁ g₂ →
      app= (TwoSemiFunctor.pres-comp group-to-EM₁→EM₂-op g₁ g₂) embase ==
      comp embase embase
    app=-group-to-EM₁→EM₂-op-pres-comp-embase g₁ g₂ = =ₛ-out $
      app= (TwoSemiFunctor.pres-comp group-to-EM₁→EM₂-op g₁ g₂) embase ◃∎
        =ₛ⟨ ap-seq-=ₛ (λ f → f embase) (comp-functors-pres-comp-β G₀₁ G₁₂ g₁ g₂) ⟩
      app= (ap (TwoSemiFunctor.F₁ G₁₂) (TwoSemiFunctor.pres-comp G₀₁ g₁ g₂)) embase ◃∙
      app= (TwoSemiFunctor.pres-comp G₁₂ (cp₀₁ g₁) (cp₀₁ g₂)) embase ◃∎
        =ₛ⟨ 0 & 1 & =ₛ-in {t = []} $
            app= (ap (λ f x → [ η (f x) ]) (λ= (cp₀₁-distr-l g₁ g₂))) embase
              =⟨ ap (λ w → app= w embase) (λ=-ap (λ _ y → [ η y ]) (cp₀₁-distr-l g₁ g₂)) ⟩
            app= (λ= (λ a → ap (λ y → [ η y ]) (cp₀₁-distr-l g₁ g₂ a))) embase
              =⟨ app=-β (λ a → ap (λ y → [ η y ]) (cp₀₁-distr-l g₁ g₂ a)) embase ⟩
            idp =∎
          ⟩
      app= (TwoSemiFunctor.pres-comp G₁₂ (cp₀₁ g₁) (cp₀₁ g₂)) embase ◃∎
        =ₛ₁⟨ app=-β (λ y → comp (cp₀₁ g₁ y) (cp₀₁ g₂ y)) embase ⟩
      comp embase embase ◃∎ ∎ₛ
      where
        G₀₁ = group-to-EM₁H→EM₁G⊗H
        G₁₂ = fun-functor-map (EM₁ H.grp) comp-functor

module CP₁₁ where

  private
    C : Type (lmax i j)
    C = EM₁ H.grp → EM G⊗H.abgroup 2

    C-level : has-level 2 C
    C-level = Π-level (λ _ → EM-level G⊗H.abgroup 2)

    D₀ : TwoSemiCategory lzero i
    D₀ = group-to-cat G.grp

    D₁' : TwoSemiCategory (lmax i j) (lmax i j)
    D₁' = =ₜ-fundamental-cat (Susp (EM₁ G⊗H.grp))

    D₁ : TwoSemiCategory (lmax i j) (lmax i j)
    D₁ = fun-cat (EM₁ H.grp) D₁'

    D₂' : TwoSemiCategory (lmax i j) (lmax i j)
    D₂' = 2-type-fundamental-cat (EM G⊗H.abgroup 2)

    D₂ : TwoSemiCategory (lmax i j) (lmax i j)
    D₂ = fun-cat (EM₁ H.grp) D₂'

    D₃ : TwoSemiCategory (lmax i j) (lmax i j)
    D₃ = 2-type-fundamental-cat (EM₁ H.grp → EM G⊗H.abgroup 2) {{C-level}}

    F₀₁ : TwoSemiFunctor D₀ D₁
    F₀₁ = group-to-EM₁→EM₂-op

    F₁₂' : TwoSemiFunctor D₁' D₂'
    F₁₂' = =ₜ-to-2-type-fundamental-cat (Susp (EM₁ G⊗H.grp))

    F₁₂ : TwoSemiFunctor D₁ D₂
    F₁₂ = fun-functor-map (EM₁ H.grp) F₁₂'

  F₀₂ : TwoSemiFunctor D₀ D₂
  F₀₂ = F₀₁ –F→ F₁₂

  module F₂₃-Funext = FunextFunctors (EM₁ H.grp) (EM G⊗H.abgroup 2) {{⟨⟩}}
  F₂₃ : TwoSemiFunctor D₂ D₃
  F₂₃ = F₂₃-Funext.λ=-functor

  module F₀₂ = TwoSemiFunctor F₀₂
  module F₂₃ = TwoSemiFunctor F₂₃

  private
    module F₀₃-Comp = FunctorComposition F₀₂ F₂₃
    F₀₃ : TwoSemiFunctor D₀ D₃
    F₀₃ = F₀₃-Comp.composition

    module F₀₁  = TwoSemiFunctor F₀₁
    module F₁₂  = TwoSemiFunctor F₁₂
    module F₁₂' = TwoSemiFunctor F₁₂'
    module F₀₃  = TwoSemiFunctor F₀₃

    module CP₁₁-Rec = EM₁Rec {G = G.grp} {C = C} {{C-level}} F₀₃

  abstract
    cp₁₁ : EM₁ G.grp → EM₁ H.grp → EM G⊗H.abgroup 2
    cp₁₁ = CP₁₁-Rec.f

    cp₁₁-embase-β : cp₁₁ embase ↦ (λ _ → [ north ])
    cp₁₁-embase-β = CP₁₁-Rec.embase-β
    {-# REWRITE cp₁₁-embase-β #-}

    cp₁₁-emloop-β : ∀ g → ap cp₁₁ (emloop g) == λ= (λ y → ap [_] (η (cp₀₁ g y)))
    cp₁₁-emloop-β g = CP₁₁-Rec.emloop-β g

    app=-F₀₂-pres-comp-embase-β : ∀ g₁ g₂ →
      app= (F₀₂.pres-comp g₁ g₂) embase ◃∎
      =ₛ
      ap (ap [_]) (comp-l embase) ◃∙
      ap-∙ [_] (η embase) (η embase) ◃∎
    app=-F₀₂-pres-comp-embase-β g₁ g₂ =
      app= (F₀₂.pres-comp g₁ g₂) embase ◃∎
        =ₛ⟨ ap-seq-=ₛ (λ f → f embase) (comp-functors-pres-comp-β F₀₁ F₁₂ g₁ g₂) ⟩
      app= (ap (λ α y → <– (=ₜ-equiv [ north ] [ north ]) (α y))
               (F₀₁.pres-comp g₁ g₂)) embase ◃∙
      app= (F₁₂.pres-comp {x = λ _ → [ north ]} {y = λ _ → [ north ]} {z = λ _ → [ north ]}
                          (λ y → [ η (cp₀₁ g₁ y) ]₁) (λ y → [ η (cp₀₁ g₂ y) ]₁)) embase ◃∎
        =ₛ₁⟨ 0 & 1 & step₂ ⟩
      ap (ap [_]) (comp-l embase) ◃∙
      app= (F₁₂.pres-comp {x = λ _ → [ north ]} {y = λ _ → [ north ]} {z = λ _ → [ north ]}
                          (λ y → [ η (cp₀₁ g₁ y) ]₁) (λ y → [ η (cp₀₁ g₂ y) ]₁)) embase ◃∎
        =ₛ₁⟨ 1 & 1 & step₃ ⟩
      ap (ap [_]) (comp-l embase) ◃∙
      ap-∙ [_] (η embase) (η embase) ◃∎ ∎ₛ
      where
      step₂ :
        app= (ap (λ α y → <– (=ₜ-equiv [ north ] [ north ]) (α y))
             (F₀₁.pres-comp g₁ g₂)) embase
        == ap (ap [_]) (comp-l embase)
      step₂ =
        app= (ap (λ α y → <– (=ₜ-equiv [ north ] [ north ]) (α y))
                 (F₀₁.pres-comp g₁ g₂)) embase
          =⟨ ∘-ap (λ f → f embase)
                  (λ α y → <– (=ₜ-equiv [ north ] [ north ]) (α y))
                  (F₀₁.pres-comp g₁ g₂) ⟩
        ap (λ α → <– (=ₜ-equiv [ north ] [ north ]) (α embase))
           (F₀₁.pres-comp g₁ g₂)
          =⟨ ap-∘ (<– (=ₜ-equiv [ north ] [ north ]))
                  (λ f → f embase)
                  (F₀₁.pres-comp g₁ g₂) ⟩
        ap (<– (=ₜ-equiv [ north ] [ north ]))
           (app= (F₀₁.pres-comp g₁ g₂) embase)
          =⟨ ap (ap (<– (=ₜ-equiv [ north ] [ north ])))
                (app=-group-to-EM₁→EM₂-op-pres-comp-embase g₁ g₂) ⟩
        ap (<– (=ₜ-equiv [ north ] [ north ])) (comp embase embase)
          =⟨ ap (ap (<– (=ₜ-equiv [ north ] [ north ])))
                (comp-unit-l embase) ⟩
        ap (<– (=ₜ-equiv [ north ] [ north ]))
           (comp-l₁ embase)
          =⟨ ∘-ap (<– (=ₜ-equiv [ north ] [ north ])) [_]₁ (comp-l embase) ⟩
        ap (ap [_]) (comp-l embase) =∎
      step₃ :
        app= (F₁₂.pres-comp {x = λ _ → [ north ]₂} {y = λ _ → [ north ]₂} {z = λ _ → [ north ]₂}
                            (λ y → [ η (cp₀₁ g₁ y) ]₁) (λ y → [ η (cp₀₁ g₂ y) ]₁)) embase
        == ap-∙ [_] (η embase) (η embase)
      step₃ =
        app= (F₁₂.pres-comp {x = λ _ → [ north ]} {y = λ _ → [ north ]} {z = λ _ → [ north ]}
                            (λ y → [ η (cp₀₁ g₁ y) ]₁) (λ y → [ η (cp₀₁ g₂ y) ]₁)) embase
           =⟨ app=-β (λ y → F₁₂'.pres-comp {x = [ north ]} {y = [ north ]} {z = [ north ]}
                                           [ η (cp₀₁ g₁ y) ]₁ [ η (cp₀₁ g₂ y) ]₁) embase ⟩
        F₁₂'.pres-comp {x = [ north ]} {y = [ north ]} {z = [ north ]} [ η embase ]₁ [ η embase ]₁
          =⟨ =ₜ-to-2-type-fundamental-cat-pres-comp-β (Susp (EM₁ G⊗H.grp)) (η embase) (η embase) ⟩
        ap-∙ [_] (η embase) (η embase) =∎

    app=-F₀₂-pres-comp-embase-coh : ∀ g₁ g₂ →
      app= (F₀₂.pres-comp g₁ g₂) embase ◃∙
      ap2 _∙_ (ap (ap [_]) (!-inv-r (merid embase)))
              (ap (ap [_]) (!-inv-r (merid embase))) ◃∎
      =ₛ
      ap (ap [_]) (!-inv-r (merid embase)) ◃∎
    app=-F₀₂-pres-comp-embase-coh g₁ g₂ =
      app= (F₀₂.pres-comp g₁ g₂) embase ◃∙
      ap2 _∙_ (ap (ap [_]) (!-inv-r (merid embase)))
              (ap (ap [_]) (!-inv-r (merid embase))) ◃∎
        =ₛ⟨ 0 & 1 & app=-F₀₂-pres-comp-embase-β g₁ g₂ ⟩
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
          → add-path-inverse-l (p ∙ ! p) p ◃∙ ap2 _∙_ (!-inv-r p) (!-inv-r p) ◃∎
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
    app= (ap cp₁₁ (emloop (G.comp g₁ g₂))) y =-= ap [_] (η (cp₀₁ g₁ y)) ∙ ap [_] (η (cp₀₁ g₂ y))
  app=-ap-cp₁₁-coh-seq₁ g₁ g₂ y =
    app= (ap cp₁₁ (emloop (G.comp g₁ g₂))) y
      =⟪ ap (λ u → app= (ap cp₁₁ u) y) (emloop-comp g₁ g₂) ⟫
    app= (ap cp₁₁ (emloop g₁ ∙ emloop g₂)) y
      =⟪ ap (λ u → app= u y) (ap-∙ cp₁₁ (emloop g₁) (emloop g₂)) ⟫
    app= (ap cp₁₁ (emloop g₁) ∙ ap cp₁₁ (emloop g₂)) y
      =⟪ ap-∙ (λ f → f y) (ap cp₁₁ (emloop g₁)) (ap cp₁₁ (emloop g₂)) ⟫
    app= (ap cp₁₁ (emloop g₁)) y ∙ app= (ap cp₁₁ (emloop g₂)) y
      =⟪ ap2 _∙_ (app=-ap-cp₁₁ g₁ y) (app=-ap-cp₁₁ g₂ y) ⟫
    ap [_] (η (cp₀₁ g₁ y)) ∙ ap [_] (η (cp₀₁ g₂ y)) ∎∎

  app=-ap-cp₁₁-coh-seq₂ : ∀ g₁ g₂ y →
    app= (ap cp₁₁ (emloop (G.comp g₁ g₂))) y =-= ap [_] (η (cp₀₁ g₁ y)) ∙ ap [_] (η (cp₀₁ g₂ y))
  app=-ap-cp₁₁-coh-seq₂ g₁ g₂ y =
    app= (ap cp₁₁ (emloop (G.comp g₁ g₂))) y
      =⟪ app=-ap-cp₁₁ (G.comp g₁ g₂) y ⟫
    ap [_] (η (cp₀₁ (G.comp g₁ g₂) y))
      =⟪ app= (F₀₂.pres-comp g₁ g₂) y ⟫
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
      ap (λ p → app= p y) (cp₁₁-emloop-β (G.comp g₁ g₂)) ◃∙
      ap (λ p → app= p y) (F₀₃.pres-comp g₁ g₂) ◃∙
      ap (λ p → app= p y) (=ₛ-out (∙-λ= (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x))))) ◃∙
      app=-β (λ x → ap [_] (η (cp₀₁ g₁ x)) ∙ ap [_] (η (cp₀₁ g₂ x))) y ◃∎
        =ₛ⟨ 1 & 2 & step₈ ⟩
      ap (λ p → app= p y) (cp₁₁-emloop-β (G.comp g₁ g₂)) ◃∙
      ap (λ p → app= p y) (ap λ= (F₀₂.pres-comp g₁ g₂)) ◃∙
      app=-β (λ x → ap [_] (η (cp₀₁ g₁ x)) ∙ ap [_] (η (cp₀₁ g₂ x))) y ◃∎
        =ₛ₁⟨ 1 & 1 & ∘-ap (λ p → app= p y) λ= (F₀₂.pres-comp g₁ g₂) ⟩
      ap (λ p → app= p y) (cp₁₁-emloop-β (G.comp g₁ g₂)) ◃∙
      ap (λ γ → app= (λ= γ) y) (F₀₂.pres-comp g₁ g₂) ◃∙
      app=-β (λ x → ap [_] (η (cp₀₁ g₁ x)) ∙ ap [_] (η (cp₀₁ g₂ x))) y ◃∎
        =ₛ⟨ 1 & 2 &
            homotopy-naturality (λ γ → app= (λ= γ) y)
                                (λ γ → γ y)
                                (λ γ → app=-β γ y)
                                (F₀₂.pres-comp g₁ g₂) ⟩
      ap (λ p → app= p y) (cp₁₁-emloop-β (G.comp g₁ g₂)) ◃∙
      app=-β (λ x → ap [_] (η (cp₀₁ (G.comp g₁ g₂) x))) y ◃∙
      app= (F₀₂.pres-comp g₁ g₂) y ◃∎
        =ₛ⟨ 0 & 2 & contract ⟩
      app=-ap-cp₁₁ (G.comp g₁ g₂) y ◃∙
      app= (F₀₂.pres-comp g₁ g₂) y ◃∎ ∎ₛ
      where
      step₈ :
        ap (λ p → app= p y) (F₀₃.pres-comp g₁ g₂) ◃∙
        ap (λ p → app= p y) (=ₛ-out (∙-λ= (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x))))) ◃∎
        =ₛ
        ap (λ p → app= p y) (ap λ= (F₀₂.pres-comp g₁ g₂)) ◃∎
      step₈ = ap-seq-=ₛ (λ p → app= p y) $
        F₀₃.pres-comp g₁ g₂ ◃∙
        =ₛ-out (∙-λ= (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x)))) ◃∎
          =ₛ⟨ 0 & 1 & F₀₃-Comp.pres-comp-β g₁ g₂ ⟩
        ap λ= (F₀₂.pres-comp g₁ g₂) ◃∙
        F₂₃.pres-comp (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x))) ◃∙
        =ₛ-out (∙-λ= (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x)))) ◃∎
          =ₛ₁⟨ 1 & 1 & F₂₃-Funext.λ=-functor-pres-comp=λ=-∙ (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x))) ⟩
        ap λ= (F₀₂.pres-comp g₁ g₂) ◃∙
        =ₛ-out (λ=-∙ (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x)))) ◃∙
        =ₛ-out (∙-λ= (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x)))) ◃∎
          =ₛ⟨ 1 & 2 & seq-!-inv-l (=ₛ-out (∙-λ= (λ x → ap [_] (η (cp₀₁ g₁ x))) (λ x → ap [_] (η (cp₀₁ g₂ x)))) ◃∎) ⟩
        ap λ= (F₀₂.pres-comp g₁ g₂) ◃∎ ∎ₛ

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
    ap (λ x → cp₁₁ x y) (emloop (G.comp g₁ g₂)) =-= ap [_] (η (cp₀₁ g₁ y)) ∙ ap [_] (η (cp₀₁ g₂ y))
  ap-cp₁₁-coh-seq₁ g₁ g₂ y =
    ap (λ x → cp₁₁ x y) (emloop (G.comp g₁ g₂))
      =⟪ ap (ap (λ x → cp₁₁ x y)) (emloop-comp g₁ g₂) ⟫
    ap (λ x → cp₁₁ x y) (emloop g₁ ∙ emloop g₂)
      =⟪ ap-∙ (λ x → cp₁₁ x y) (emloop g₁) (emloop g₂) ⟫
    ap (λ x → cp₁₁ x y) (emloop g₁) ∙ ap (λ x → cp₁₁ x y) (emloop g₂)
      =⟪ ap2 _∙_ (ap-cp₁₁ g₁ y) (ap-cp₁₁ g₂ y) ⟫
    ap [_] (η (cp₀₁ g₁ y)) ∙ ap [_] (η (cp₀₁ g₂ y)) ∎∎

  ap-cp₁₁-coh-seq₂ : ∀ g₁ g₂ y →
    ap (λ x → cp₁₁ x y) (emloop (G.comp g₁ g₂)) =-= ap [_] (η (cp₀₁ g₁ y)) ∙ ap [_] (η (cp₀₁ g₂ y))
  ap-cp₁₁-coh-seq₂ g₁ g₂ y =
    ap (λ x → cp₁₁ x y) (emloop (G.comp g₁ g₂))
      =⟪ ap-cp₁₁ (G.comp g₁ g₂) y ⟫
    ap [_] (η (cp₀₁ (G.comp g₁ g₂) y))
      =⟪ app= (F₀₂.pres-comp g₁ g₂) y ⟫
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
        =ₛ⟨ 0 & 2 & homotopy-naturality {A = embase' G.grp == embase} {B = cp₁₁ embase y == cp₁₁ embase y}
                                        (ap (λ x → cp₁₁ x y)) (λ p → app= (ap cp₁₁ p) y)
                                        (ap-∘ (λ f → f y) cp₁₁) (emloop-comp g₁ g₂) ⟩
      ap-∘ (λ f → f y) cp₁₁ (emloop (G.comp g₁ g₂)) ◃∙
      ap (λ p → app= (ap cp₁₁ p) y) (emloop-comp g₁ g₂) ◃∙
      ap (ap (λ f → f y)) (ap-∙ cp₁₁ (emloop g₁) (emloop g₂)) ◃∙
      ap-∙ (λ f → f y) (ap cp₁₁ (emloop g₁)) (ap cp₁₁ (emloop g₂)) ◃∙
      ap2 _∙_ (app=-ap-cp₁₁ g₁ y) (app=-ap-cp₁₁ g₂ y) ◃∎
        =ₛ⟨ 1 & 4 & app=-ap-cp₁₁-coh g₁ g₂ y ⟩
      ap-∘ (λ f → f y) cp₁₁ (emloop (G.comp g₁ g₂)) ◃∙
      app=-ap-cp₁₁ (G.comp g₁ g₂) y ◃∙
      app= (F₀₂.pres-comp g₁ g₂) y ◃∎
        =ₛ₁⟨ 0 & 2 & idp ⟩
      ap-cp₁₁ (G.comp g₁ g₂) y ◃∙
      app= (F₀₂.pres-comp g₁ g₂) y ◃∎ ∎ₛ

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
    ap (λ x → cp₁₁ x embase) (emloop (G.comp g₁ g₂)) =-= idp
  ap-cp₁₁-embase-coh-seq g₁ g₂ =
    ap (λ x → cp₁₁ x embase) (emloop (G.comp g₁ g₂))
      =⟪ ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ⟫
    ap (λ x → cp₁₁ x embase) (emloop g₁ ∙ emloop g₂)
      =⟪ ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂) ⟫
    ap (λ x → cp₁₁ x embase) (emloop g₁) ∙ ap (λ x → cp₁₁ x embase) (emloop g₂)
      =⟪ ap2 _∙_ (ap-cp₁₁-embase g₁) (ap-cp₁₁-embase g₂) ⟫
    idp ∎∎

  ap-cp₁₁-embase-coh : ∀ g₁ g₂ →
    ap-cp₁₁-embase (G.comp g₁ g₂) ◃∎ =ₛ ap-cp₁₁-embase-coh-seq g₁ g₂
  ap-cp₁₁-embase-coh g₁ g₂ =
    ap-cp₁₁-embase (G.comp g₁ g₂) ◃∎
      =ₛ⟨ expand (ap-cp₁₁-embase-seq (G.comp g₁ g₂)) ⟩
    ap-cp₁₁ (G.comp g₁ g₂) embase ◃∙
    ap (ap [_]) (!-inv-r (merid embase)) ◃∎
      =ₛ⟨ 1 & 1 & !ₛ (app=-F₀₂-pres-comp-embase-coh g₁ g₂) ⟩
    ap-cp₁₁ (G.comp g₁ g₂) embase ◃∙
    app= (F₀₂.pres-comp g₁ g₂) embase ◃∙
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

open CP₁₁ public
