{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Connected

-- TODO Use pType i?
module Homotopy.Cover {i} (A : Set i) (a : A)
  (A-is-conn : is-connected ⟨0⟩ A) where

open import HLevel
open import Homotopy.Truncation
open import Homotopy.PathTruncation
open import Homotopy.Pointed
open import Integers
open import Homotopy.HomotopyGroups
open import Spaces.Pi0Paths
open import Algebra.Groups

record covering : Set (suc i) where
  constructor cov[_,_]
  field
    fiber : A → Set i
    fiber-is-set : ∀ a → is-set (fiber a)

-- In terms of connectedness
is-universal : covering → Set i
is-universal cov[ fiber , _ ] = is-connected ⟨1⟩ $ Σ A fiber

-- In terms of connectedness
universal-covering : Set (suc i)
universal-covering = Σ covering is-universal

tracing : ∀ cov → let open covering cov in
  ∀ {a₁ a₂} → fiber a₁ → a₁ ≡₀ a₂ → fiber a₂
tracing cov[ fiber , fiber-is-set ] y =
  π₀-extend-nondep
    ⦃ fiber-is-set _ ⦄
    (λ p → transport fiber p y)

compose-tracing : ∀ cov → let open covering cov in
  ∀ {a₁ a₂ a₃} y (p₁ : a₁ ≡₀ a₂) (p₂ : a₂ ≡₀ a₃)
  → tracing cov (tracing cov y p₁) p₂ ≡ tracing cov y (p₁ ∘₀ p₂)
compose-tracing cov y = let open covering cov in
  π₀-extend
    ⦃ λ _ → Π-is-set λ _ → ≡-is-set $ fiber-is-set _ ⦄
    (λ p₁ → π₀-extend
      ⦃ λ _ → ≡-is-set $ fiber-is-set _ ⦄
      (λ p₂ → compose-trans fiber p₂ p₁ y))

covering-eq : ∀ {co₁ co₂ : covering}
  → covering.fiber co₁ ≡ covering.fiber co₂
  → co₁ ≡ co₂
covering-eq {cov[ ._ , set₁ ]} {cov[ ._ , set₂ ]} (refl _) =
  ap (λ set → cov[ _ , set ])
    (prop-has-all-paths (Π-is-prop λ _ → is-set-is-prop) _ _)

module Reconstruct where
  private
    fundamental-group : group i
    fundamental-group = πⁿ-group 1 (A , a)
    module G = group fundamental-group

  open import Algebra.GroupSets fundamental-group
  open import Homotopy.Cover.Ribbon A a

  {-
    ribbon-is-covering : ∀ {Y} → action Y → covering
    ribbon-is-covering act = cov ribbon act , ribbon-is-set act
  -}

  -- G-set <-> cover
  module _ where
    open import Homotopy.Skeleton

    gset⇒covering : gset → covering
    gset⇒covering gset[ _ , act , _ ] = cov[ ribbon act , ribbon-is-set ]

    covering⇒action : ∀ cov → action (covering.fiber cov a)
    covering⇒action cov = act[ tracing cov , refl , compose-tracing cov ]

    covering⇒gset : covering → gset
    covering⇒gset cov = let open covering cov in
      gset[ fiber a , covering⇒action cov , fiber-is-set a ]

    -- The first direction: covering -> gset -> covering

    fiber+path⇒ribbon : ∀ cov a₂ y (p : a ≡ a₂) → ribbon (covering⇒action cov) a₂
    fiber+path⇒ribbon cov a₂ y p = trace (tracing cov y (proj $ ! p)) (proj p)

    fiber+path⇒ribbon-is-path-irrelevant : ∀ cov a₂ y p₁ p₂
      → fiber+path⇒ribbon cov a₂ y p₁ ≡ fiber+path⇒ribbon cov a₂ y p₂
    fiber+path⇒ribbon-is-path-irrelevant cov a₂ y p₁ p₂ =
      -- FIXME The whole proof should be in reverse to reduce !
      trace (tracing cov y (proj $ ! p₁)) (proj p₁)
        ≡⟨ ap (λ x → trace (tracing cov y (proj $ ! p₁)) (proj x))
              $ ! $ refl-right-unit p₁ ⟩
      trace (tracing cov y (proj $ ! p₁)) (proj $ p₁ ∘ refl _)
        ≡⟨ ap (λ x → trace (tracing cov y (proj $ ! p₁)) (proj $ p₁ ∘ x))
              $ ! $ opposite-left-inverse p₂ ⟩
      trace (tracing cov y (proj $ ! p₁)) (proj $ p₁ ∘ (! p₂ ∘ p₂))
        ≡⟨ ap (λ x → trace (tracing cov y (proj $ ! p₁)) (proj x))
              $ ! $ concat-assoc p₁ (! p₂) p₂ ⟩
      trace (tracing cov y (proj $ ! p₁)) (proj $ (p₁ ∘ ! p₂) ∘ p₂)
        ≡⟨ ! $ paste (tracing cov y (proj $ ! p₁)) (proj $ p₁ ∘ ! p₂) (proj p₂) ⟩
      trace (tracing cov (tracing cov y (proj $ ! p₁)) (proj (p₁ ∘ ! p₂))) (proj p₂)
        ≡⟨ ap (λ x → trace x (proj p₂))
              $ compose-tracing cov y (proj $ ! p₁) (proj $ p₁ ∘ ! p₂) ⟩
      trace (tracing cov y (proj $ ! p₁ ∘ (p₁ ∘ ! p₂))) (proj p₂)
        ≡⟨ ap (λ x → trace (tracing cov y (proj x)) (proj p₂))
              $ ! $ concat-assoc (! p₁) p₁ (! p₂) ⟩
      trace (tracing cov y (proj $ (! p₁ ∘ p₁) ∘ ! p₂)) (proj p₂)
        ≡⟨ ap (λ x → trace (tracing cov y (proj $ x ∘ ! p₂)) (proj p₂))
              $ opposite-left-inverse p₁ ⟩∎
      trace (tracing cov y (proj $ ! p₂)) (proj p₂)
        ∎

    private
      skel : ∀ cov (a₂ : A) → covering.fiber cov a₂ → Set i
      skel cov a₂ y = π₀ (skeleton₁ (fiber+path⇒ribbon cov a₂ y))

    abstract
      skel-has-all-paths : ∀ cov a₂ y → has-all-paths (skel cov a₂ y)
      skel-has-all-paths cov a₂ y =
        π₀-extend ⦃ λ _ → Π-is-set λ _ → ≡-is-set $ π₀-is-set _ ⦄
          (skeleton₁-rec (λ s₁ → ∀ s₂ → proj s₁ ≡ s₂)
            (λ p₁ → π₀-extend ⦃ λ _ → ≡-is-set $ π₀-is-set _ ⦄
              (skeleton₁-rec (λ s₂ → proj (point p₁) ≡ proj s₂)
                (λ p₂ → ap proj $ link p₁ p₂
                                $ fiber+path⇒ribbon-is-path-irrelevant cov a₂ y p₁ p₂)
                (λ _ _ _ → prop-has-all-paths (π₀-is-set _ _ _) _ _)))
            (λ _ _ _ → funext λ _ → prop-has-all-paths (π₀-is-set _ _ _) _ _))

    skel-is-prop : ∀ cov a₂ y → is-prop (skel cov a₂ y)
    skel-is-prop cov a₂ y = all-paths-is-prop $ skel-has-all-paths cov a₂ y

    fiber+skel⇒ribbon : ∀ cov a₂ y → skel cov a₂ y → ribbon (covering⇒action cov) a₂
    fiber+skel⇒ribbon cov a₂ y = π₀-extend-nondep ⦃ ribbon-is-set a₂ ⦄ skeleton₁-lifted

    private
      base-path-magic : ∀ a₂ → [ a ≡ a₂ ]
      base-path-magic = connected-has-all-τ-paths A-is-conn a

      skel-magic : ∀ cov a₂ y → skel cov a₂ y
      skel-magic cov a₂ y = []-extend-nondep ⦃ skel-is-prop cov a₂ y ⦄
        (proj ◯ point) (base-path-magic a₂)

    fiber⇒ribbon : ∀ cov a₂ → covering.fiber cov a₂ → ribbon (covering⇒action cov) a₂
    fiber⇒ribbon cov a₂ y = fiber+skel⇒ribbon cov a₂ y $ skel-magic cov a₂ y

    ribbon⇒fiber : ∀ cov a₂ → ribbon (covering⇒action cov) a₂ → covering.fiber cov a₂
    ribbon⇒fiber cov a₂ = let open covering cov in
      ribbon-rec-nondep a₂ (fiber a₂) ⦃ fiber-is-set a₂ ⦄ (tracing cov) (compose-tracing cov)

    abstract
      ribbon⇒fiber⇒ribbon : ∀ cov a₂ r → fiber⇒ribbon cov a₂ (ribbon⇒fiber cov a₂ r) ≡ r
      ribbon⇒fiber⇒ribbon cov a₂ = ribbon-rec a₂
        (λ r → fiber⇒ribbon cov a₂ (ribbon⇒fiber cov a₂ r) ≡ r)
        ⦃ λ _ → ≡-is-set $ ribbon-is-set a₂ ⦄
        (λ y p → []-extend
          -- All these ugly things will go away when bp = proj bp′
          ⦃ λ bp → ribbon-is-set a₂
                    (fiber+skel⇒ribbon cov a₂ (tracing cov y p)
                      ([]-extend-nondep
                        ⦃ skel-is-prop cov a₂ (tracing cov y p) ⦄
                        (proj ◯ point) bp))
                    (trace y p) ⦄
          (λ bp → -- real base path
              trace (tracing cov (tracing cov y p) (proj $ ! bp)) (proj bp)
                ≡⟨ ap (λ x → trace x (proj bp)) $ compose-tracing cov y p (proj $ ! bp) ⟩
              trace (tracing cov y (p ∘₀ proj (! bp))) (proj bp)
                ≡⟨ paste y (p ∘₀ proj (! bp)) (proj bp) ⟩
              trace y ((p ∘₀ proj (! bp)) ∘₀ proj bp)
                ≡⟨ ap (trace y) $ concat₀-assoc p (proj $ ! bp) (proj bp) ⟩
              trace y (p ∘₀ (proj $ ! bp ∘ bp))
                ≡⟨ ap (λ x → trace y (p ∘₀ proj x)) $ opposite-left-inverse bp ⟩
              trace y (p ∘₀ refl₀ _)
                ≡⟨ ap (trace y) $ refl₀-right-unit p ⟩∎
              trace y p
                ∎)
          (base-path-magic a₂))
        (λ _ _ _ → prop-has-all-paths (ribbon-is-set a₂ _ _) _ _)

      fiber⇒ribbon⇒fiber : ∀ cov a₂ y → ribbon⇒fiber cov a₂ (fiber⇒ribbon cov a₂ y) ≡ y
      fiber⇒ribbon⇒fiber cov a₂ y = let open covering cov in []-extend
        ⦃ λ bp → fiber-is-set a₂
                  (ribbon⇒fiber cov a₂
                    (fiber+skel⇒ribbon cov a₂ y
                      ([]-extend-nondep
                        ⦃ skel-is-prop cov a₂ y ⦄
                        (proj ◯ point) bp)))
                  y ⦄
        ( λ bp →
            tracing cov (tracing cov y (proj $ ! bp)) (proj bp)
              ≡⟨ compose-tracing cov y (proj $ ! bp) (proj bp) ⟩
            tracing cov y (proj $ ! bp ∘ bp)
              ≡⟨ ap (tracing cov y ◯ proj) $ opposite-left-inverse bp ⟩∎
            y
              ∎)
        (base-path-magic a₂)

    covering⇒gset⇒covering : ∀ cov → gset⇒covering (covering⇒gset cov) ≡ cov
    covering⇒gset⇒covering cov = covering-eq $ funext λ a₂
      → eq-to-path $ ribbon⇒fiber cov a₂ , iso-is-eq
          (ribbon⇒fiber cov a₂)
          (fiber⇒ribbon cov a₂)
          (fiber⇒ribbon⇒fiber cov a₂)
          (ribbon⇒fiber⇒ribbon cov a₂)

    -- The second direction : gset -> covering -> gset

    ribbon-a⇒Y : ∀ {Y} {act : action Y} ⦃ _ : is-set Y ⦄ → ribbon act a → Y
    ribbon-a⇒Y {Y} {act} ⦃ Y-is-set ⦄ = let open action act in
      ribbon-rec-nondep a Y ⦃ Y-is-set ⦄ _∙_ assoc

    ribbon-a≃Y : ∀ {Y} {act : action Y} ⦃ _ : is-set Y ⦄ → ribbon act a ≃ Y
    ribbon-a≃Y {Y} {act} ⦃ Y-is-set ⦄ = let open action act in
      ribbon-a⇒Y ⦃ Y-is-set ⦄ , iso-is-eq _
        (λ y → trace y (refl₀ _))
        (λ y → right-unit y)
        (ribbon-rec a
          (λ r → trace (ribbon-a⇒Y ⦃ Y-is-set ⦄ r) (refl₀ _) ≡ r)
          ⦃ λ _ → ≡-is-set $ ribbon-is-set a ⦄
          (λ y p →
            trace (y ∙ p) (refl₀ _)
              ≡⟨ paste y p (refl₀ _) ⟩
            trace y (p G.∙ refl₀ _)
              ≡⟨ ap (trace y) $ G.right-unit p ⟩∎
            trace y p
              ∎)
          (λ _ _ _ → prop-has-all-paths (ribbon-is-set a _ _) _ _))

    trans-eq-∙ : ∀ {Y₁ Y₂ : Set i} (Y≃ : Y₁ ≃ Y₂) (_∙_ : Y₁ → G.elems → Y₁) (y₂ : Y₂) (g : G.elems)
      → transport (λ Y → Y → G.elems → Y) (eq-to-path Y≃) _∙_ y₂ g ≡ (Y≃ ☆ (inverse Y≃ y₂ ∙ g))
    trans-eq-∙ = equiv-induction
      (λ {Y₁ Y₂ : Set i} (Y≃ : Y₁ ≃ Y₂)
        → ∀ (_∙_ : Y₁ → G.elems → Y₁) (y₂ : Y₂) (g : G.elems)
        → transport (λ Y → Y → G.elems → Y) (eq-to-path Y≃) _∙_ y₂ g ≡ (Y≃ ☆ (inverse Y≃ y₂ ∙ g)))
      (λ Y _∙_ y₂ g → ap (λ x → transport (λ Y → Y → G.elems → Y) x _∙_ y₂ g)
                         $ path-to-eq-right-inverse $ refl _)

    gset⇒covering⇒gset : ∀ gs → covering⇒gset (gset⇒covering gs) ≡ gs
    gset⇒covering⇒gset gset[ Y , act , Y-is-set ] =
      let
        open action act
        _⊙_ = tracing cov[ ribbon act , ribbon-is-set {Y} {act} ]
        ≃Y = ribbon-a≃Y ⦃ Y-is-set ⦄
        ⇒Y = ribbon-a⇒Y ⦃ Y-is-set ⦄
      in gset-eq
          (eq-to-path ≃Y)
          (funext λ y → funext $ π₀-extend ⦃ λ _ → ≡-is-set Y-is-set ⦄ λ p →
            transport (λ Y → Y → G.elems → Y) (eq-to-path ≃Y) _⊙_ y (proj p)
              ≡⟨ trans-eq-∙ ≃Y _⊙_ y (proj p) ⟩
            ⇒Y (transport (ribbon act) p (trace y (refl₀ _)))
              ≡⟨ ap ⇒Y $ trans-trace act p y (refl₀ _) ⟩∎
            y ∙ proj p
              ∎)

    -- Finally...

    gset-covering-eq : gset ≃ covering
    gset-covering-eq = gset⇒covering , iso-is-eq _ covering⇒gset
                          covering⇒gset⇒covering
                          gset⇒covering⇒gset

-- The following is still a mess.  Don't read it.
module _ (uc : universal-covering) where
  open covering (π₁ uc)

{-
  path⇒deck-is-equiv : ∀ {a₂} (path : a ≡ a₂) → is-equiv (path⇒deck path)
  path⇒deck-is-equiv path = iso-is-eq
    (transport fiber path)
    (transport fiber (! path))
    (trans-trans-opposite fiber path)
    (trans-opposite-trans fiber path)
-}

  is-nature : (fiber a → fiber a) → Set i
  is-nature f = (p : a ≡ a)
    → ∀ x → transport fiber p (f x) ≡ f (transport fiber p x)

  auto : Set i
  auto = fiber a ≃ fiber a

  -- This Lemma can be made more general as "(m+1)-connected => has-all-paths_m"
  uc-has-all-path₀ : ∀ (p q : Σ A fiber) → p ≡₀ q
  uc-has-all-path₀ p q = inverse τ-path-equiv-path-τ-S
    $ π₂ (π₂ uc) (proj p) ∘ ! (π₂ (π₂ uc) $ proj q)

  nature-auto-eq : ∀ (f₁ f₂ : auto)
    → (f₁-is-nature : is-nature (π₁ f₁))
    → (f₂-is-nature : is-nature (π₁ f₂))
    → Σ (fiber a) (λ x → f₁ ☆ x ≡ f₂ ☆ x)
    → f₁ ≡ f₂
  nature-auto-eq f₁ f₂ f₁-nat f₂-nat (x , path) = equiv-eq $ funext λ y →
    π₀-extend
      ⦃ λ _ → ≡-is-set {x = f₁ ☆ y} {y = f₂ ☆ y} $ fiber-is-set a ⦄
      (λ uc-path →
        f₁ ☆ y
          ≡⟨ ap (π₁ f₁) $ ! $ fiber-path uc-path ⟩
        f₁ ☆ transport fiber (base-path uc-path) x
          ≡⟨ ! $ f₁-nat (base-path uc-path) x ⟩
        transport fiber (base-path uc-path) (f₁ ☆ x)
          ≡⟨ ap (transport fiber $ base-path uc-path) path ⟩
        transport fiber (base-path uc-path) (f₂ ☆ x)
          ≡⟨ f₂-nat (base-path uc-path) x ⟩
        f₂ ☆ transport fiber (base-path uc-path) x
          ≡⟨ ap (π₁ f₂) $ fiber-path uc-path ⟩∎
        f₂ ☆ y
          ∎)
      (uc-has-all-path₀ (a , x) (a , y))
