{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module stash.modalities.Orthogonality where

  module _ {ℓ} where

    Δ : (A : Type ℓ) (X : Type ℓ) → A → (X → A)
    Δ A X = cst

    ⟦_⊥_⟧ : (X : Type ℓ) (A : Type ℓ) → Type _
    ⟦ A ⊥ X ⟧ = is-equiv (Δ X A)

    ⊤-orthogonal : (A : Type ℓ) → ⟦ Lift ⊤ ⊥ A ⟧
    ⊤-orthogonal A = record {
      g = λ φ → φ (lift unit) ;
      f-g = λ φ → λ= (λ { (lift unit) → idp }) ;
      g-f = λ a → idp ;
      adj = λ a → λ=-η idp }

    equiv-preserves-orth-l : {A B X : Type ℓ} → (A ≃ B) → ⟦ A ⊥ X ⟧ → ⟦ B ⊥ X ⟧
    equiv-preserves-orth-l {A} {B} {X} (f , f-ise) ω = is-eq (Δ X B) g f-g ω.g-f

      where module ω = is-equiv ω
            module f = is-equiv f-ise

            g : (B → X) → X
            g φ = ω.g (φ ∘ f)

            f-g : (φ : B → X) → Δ X B (g φ) == φ
            f-g φ = λ= λ b → app= (ω.f-g (φ ∘ f)) (f.g b) ∙ ap φ (f.f-g b)

    equiv-preserves-orth-r : {A X Y : Type ℓ} → (X ≃ Y) → ⟦ A ⊥ X ⟧ → ⟦ A ⊥ Y ⟧
    equiv-preserves-orth-r {A} {X} {Y} (f , f-ise) ω = is-eq (Δ Y A) g f-g g-f

      where module ω = is-equiv ω
            module f = is-equiv f-ise

            g : (A → Y) → Y
            g φ = f (ω.g (f.g ∘ φ))

            f-g : (φ : A → Y) → Δ Y A (g φ) == φ
            f-g φ = λ= λ x → ap f (app= (ω.f-g (f.g ∘ φ)) x) ∙ f.f-g (φ x)

            g-f : (y : Y) → g (Δ Y A y) == y
            g-f y = ap f (ω.g-f (f.g y)) ∙ f.f-g y

    -- e-orth : {A B X : Type ℓ} → ⟦ A ⊥ X ⟧ → (A ≃ B) → ⟦ B ⊥ X ⟧

    prod-to : {A B X : Type ℓ} → ⟦ A ⊥ X ⟧ → ⟦ B ⊥ X ⟧ → ⟦ A × B ⊥ X ⟧
    prod-to e f = is-eq _ (λ φ → is-equiv.g e (λ a → is-equiv.g f (λ b → φ (a , b))))
      (λ φ → λ= (λ { (a , b) → app= (is-equiv.f-g e (λ a → is-equiv.g f (λ b → φ (a , b)))) a ∙ app= (is-equiv.f-g f (λ b → φ (a , b))) b }))
      (λ x → ap (is-equiv.g e) (λ= (λ a → is-equiv.g-f f x)) ∙ is-equiv.g-f e x)

  --   ⟦_⊥_⟧ₗ : {I : Type ℓ} (X : I → Type ℓ) (A : Type ℓ) → Type ℓ
  --   ⟦_⊥_⟧ₗ {I = I} X A = (i : I) → ⟦ X i ⊥ A ⟧ₒ

  --   ⟦_⊥_⟧ᵣ : {I : Type ℓ} (X : Type ℓ) (A : I → Type ℓ) → Type ℓ
  --   ⟦_⊥_⟧ᵣ {I = I} X A = (i : I) → ⟦ X ⊥ A i ⟧ₒ

  --   ⟦_⊥_⟧ : {I J : Type ℓ} (X : I → Type ℓ) (A : J → Type ℓ) → Type ℓ
  --   ⟦_⊥_⟧ {I} {J} X A = (i : I) → (j : J) → ⟦ X i ⊥ A j ⟧ₒ

  --   cone-of : {A B : Type ℓ} → (A → B) → Type ℓ
  --   cone-of {A} {B} f = hfiber (Δ B A) f

  --   orth-to-contr-cones : {A B : Type ℓ} → ⟦ A ⊥ B ⟧ₒ → (f : A → B) → is-contr (cone-of f)
  --   orth-to-contr-cones is-orth f = equiv-is-contr-map is-orth f

  --   contr-cones-to-orth : {A B : Type ℓ} → (ε : (f : A → B) → is-contr (cone-of f)) → ⟦ A ⊥ B ⟧ₒ
  --   contr-cones-to-orth ε = contr-map-is-equiv ε

  -- -- module _ {ℓ} {X Y Z : Type ℓ} where

  -- --   jn-adj : (X * Y → Z) ≃ Σ (Y → Z) (λ φ → (x : X) → cone-of φ)
  -- --   jn-adj = equiv to from {!!} {!!}

  -- --     where to : (X * Y → Z) → Σ (Y → Z) (λ φ → (x : X) → cone-of φ)
  -- --           to φ = (φ ∘ right , (λ x → φ (left x) , λ= (λ y → ap φ (glue (x , y)))))

  -- --           from : Σ (Y → Z) (λ φ → (x : X) → cone-of φ) → (X * Y → Z)
  -- --           from (f , c) = PushoutRec.f (λ x → fst (c x)) f (λ { (x , y) → app= (snd (c x)) y })

  -- --   jn-ideal : ⟦ Y ⊥ Z ⟧ₒ → ⟦ X * Y ⊥ Z ⟧ₒ
  -- --   jn-ideal o = contr-cones-to-orth (λ φ → (is-equiv.g o (φ ∘ right) , {!!}) , {!!})

  -- module _ {ℓ} {I J : Type ℓ} where

  --   -- Pushout product (fiberwise join)
  --   _□_ : (X : I → Type ℓ) (Y : J → Type ℓ) → I × J → Type ℓ
  --   (X □ Y) (i , j) = X i * Y j

  --   -- Fiberwise diagonal (fibered version)
  --   ⟪_,_⟫ : (X : I → Type ℓ) (Y : J → Type ℓ) → (i : I) → (j : J) → (X i → Y j) → Type ℓ
  --   ⟪ X , Y ⟫ i j f = cone-of f

  --   -- Fiberwise diagonal (map version)
  --   ⟪_,_⟫₀ : (X : I → Type ℓ) (Y : J → Type ℓ) → (i : I) → (j : J) → Y j → (X i → Y j)
  --   ⟪ X , Y ⟫₀ a b y x = y

  --   fb-diag-orth : (X : I → Type ℓ) (Y : J → Type ℓ) →
  --                  ⟦ X ⊥ Y ⟧ → (i : I) → (j : J) → (f : X i → Y j) → is-contr (⟪ X , Y ⟫ i j f)
  --   fb-diag-orth X Y ε i j f = orth-to-contr-cones (ε i j) f

  -- -- module _ {ℓ} {I J K : Type ℓ} where

  -- --   thm : (X : I → Type ℓ) (Y : J → Type ℓ) (Z : K → Type ℓ)
  -- --         (i : I) (j : J) (k : K) (f : X i * Y j → Z k) →
  -- --         ⟪ X □ Y , Z ⟫ (i , j) k f ≃ ⟪ X , ⟪ Y , Z ⟫ j k ⟫ i (λ y → f (right y)) (λ x → (f (left x)) , λ= (λ y → ap f (glue (x , y))))
  -- --   thm = {!!}

  -- Is there a direct definition of a hyper-proposition?
  -- That is, without passing through the nullification functor?
  -- For example, using orthogonality?
  module _ {ℓ} where

    _≻_ : Type ℓ → Type ℓ → Type (lsucc ℓ)
    A ≻ B = (X : Type ℓ) → ⟦ B ⊥ X ⟧ → ⟦ A ⊥ X ⟧

    equiv-≻ : {A B C : Type ℓ} → A ≻ C → A ≃ B → B ≻ C
    equiv-≻ A≻C A≃B X C⊥X = equiv-preserves-orth-l A≃B (A≻C X C⊥X)

    ≻-trivial : (A : Type ℓ) → (Lift ⊤) ≻ A
    ≻-trivial A X ω = ⊤-orthogonal X

    ≻-reflexive : (A : Type ℓ) → A ≻ A
    ≻-reflexive A Y x = x

    ≻-trans : (A B C : Type ℓ) → A ≻ B → B ≻ C → A ≻ C
    ≻-trans A B C ω₀ ω₁ Y cy = ω₀ Y (ω₁ Y cy)

    diag-equiv-lem : (A : Type ℓ) → is-equiv (Δ A A) → is-contr A
    diag-equiv-lem A e = is-equiv.g e (idf A) , (λ a → app= (is-equiv.f-g e (idf A)) a)

    self-ortho-contr : (A : Type ℓ) → ⟦ A ⊥ A ⟧ → is-contr A
    self-ortho-contr A ω = diag-equiv-lem A ω

    ≻-⊤-is-contr : (A : Type ℓ) → A ≻ (Lift ⊤) → is-contr A
    ≻-⊤-is-contr A ω = self-ortho-contr A (ω A (⊤-orthogonal A))

    -- We jump a universe level, but its certainly convenient ...
    is-hyper-prop : Type ℓ → Type (lsucc ℓ)
    is-hyper-prop A = (X Y : Type ℓ) (f : X → Y) → X ≻ A → Y ≻ A → (y : Y) → hfiber f y ≻ A

    hyper-prop-kills-paths : (A : Type ℓ) → is-hyper-prop A → (a₀ a₁ : A) → a₀ == a₁ ≻ A
    hyper-prop-kills-paths A hp a₀ a₁ =
      equiv-≻ (hp (Lift ⊤) A (λ _ → a₀) (≻-trivial A) (≻-reflexive A) a₁)
      (equiv (λ { (lift unit , p) → p }) (λ p → (lift unit , p))
             (λ p → idp) (λ { (lift unit , p) → idp }))
