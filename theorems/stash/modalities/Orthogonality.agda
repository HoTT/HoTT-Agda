{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module stash.modalities.Orthogonality where

  module PathSplit {i} (X : Type i) (x y : X) where

    to : (x == y) → Σ X (λ z → (x == z) × (z == y))
    to p = x , (idp , p)

    from : Σ X (λ z → (x == z) × (z == y)) → x == y
    from (z , p , q) = p ∙ q

    abstract
    
      to-from : (b : Σ X (λ z → (x == z) × (z == y))) → to (from b) == b
      to-from (z , p , q) = pair= p (↓-×-in (↓-cst=idf-in (∙'-unit-l p)) (↓-idf=cst-in idp))

      from-to : (p : x == y) → from (to p) == p
      from-to p = idp
    
    path-split : (x == y) ≃ Σ X (λ z → (x == z) × (z == y))
    path-split = equiv to from to-from from-to

  module _ {i} where
  
    Δ : (A : Type i) (X : Type i) → A → (X → A)
    Δ A X = cst

    ⟦_⊥_⟧ : (X : Type i) (A : Type i) → Type _
    ⟦ X ⊥ A ⟧ = is-equiv (Δ A X)

    Unit-orth : (A : Type i) → ⟦ Lift ⊤ ⊥ A ⟧
    Unit-orth A = record {
      g = λ φ → φ (lift unit) ;
      f-g = λ φ → λ= (λ { (lift unit) → idp }) ;
      g-f = λ a → idp ;
      adj = λ a → λ=-η idp }

    Δ-equiv-is-contr : (A : Type i) → is-equiv (Δ A A) → is-contr A
    Δ-equiv-is-contr A e = is-equiv.g e (idf A) , (λ a → app= (is-equiv.f-g e (idf A)) a)
  
    self-orth-is-contr : (A : Type i) → ⟦ A ⊥ A ⟧ → is-contr A
    self-orth-is-contr A ω = Δ-equiv-is-contr A ω

    orth-emap : {A B X : Type i} → ⟦ A ⊥ X ⟧ → (A ≃ B) → ⟦ B ⊥ X ⟧
    orth-emap {A} {B} {X} ω e = is-eq (Δ X B) g f-g g-f

      where g : (B → X) → X
            g φ = is-equiv.g ω (φ ∘ (fst e))

            f-g : (φ : B → X) → Δ X B (g φ) == φ
            f-g φ = λ= (λ b → app= (is-equiv.f-g ω (φ ∘ (fst e))) (<– e b) ∙ ap φ (<–-inv-r e b) )

            g-f : (x : X) → g (Δ X B x) == x
            g-f x = is-equiv.g-f ω x

    prod-to : {A B X : Type i} → ⟦ A ⊥ X ⟧ → ⟦ B ⊥ X ⟧ → ⟦ A × B ⊥ X ⟧
    prod-to e f = is-eq _ (λ φ → is-equiv.g e (λ a → is-equiv.g f (λ b → φ (a , b))))
      (λ φ → λ= (λ { (a , b) → app= (is-equiv.f-g e (λ a → is-equiv.g f (λ b → φ (a , b)))) a ∙ app= (is-equiv.f-g f (λ b → φ (a , b))) b }))
      (λ x → ap (is-equiv.g e) (λ= (λ a → is-equiv.g-f f x)) ∙ is-equiv.g-f e x)

    -- This is a special case of a more general result, but I'll prove
    -- it directly here first.
    pths-orth : {A X : Type i} {x y : X} → ⟦ A ⊥ X ⟧ → ⟦ A ⊥ x == y ⟧
    pths-orth {A} {X} {x} {y} ω = is-eq (Δ (x == y) A) g {!!} {!!}

      where θ : (A → X) → X
            θ = is-equiv.g ω

            g : (A → x == y) → x == y
            g φ = p ∙ q

              where module PS = PathSplit X x y

                    z : X
                    z = θ (fst ∘ (–> PS.path-split) ∘ φ)

                    p : x == z
                    p = ! (is-equiv.g-f ω x) ∙ ap θ (λ= (fst ∘ snd ∘ (–> PS.path-split) ∘ φ))

                    q : z == y
                    q = ap θ (λ= (snd ∘ snd ∘ (–> PS.path-split) ∘ φ)) ∙ is-equiv.g-f ω y


  -- Weak cellular inequalities
  module _ {i} where
  
    _≻_ : Type i → Type i → Type _
    X ≻ A = (Y : Type i) → ⟦ A ⊥ Y ⟧ → ⟦ X ⊥ Y ⟧

    equiv-≻ : {X Y : Type i} {A : Type i} → X ≻ A → X ≃ Y → Y ≻ A
    equiv-≻ {X} {Y} {A} ω e Z o = orth-emap (ω Z o) e

    ≻-trivial : (A : Type i) → (Lift ⊤) ≻ A
    ≻-trivial A X _ = Unit-orth X
  
    ≻-reflexive : (A : Type i) → A ≻ A
    ≻-reflexive A Y x = x

    ≻-trans : (A B C : Type i) → A ≻ B → B ≻ C → A ≻ C
    ≻-trans A B C ω₀ ω₁ Y cy = ω₀ Y (ω₁ Y cy)
            
    ≻-⊤-is-contr : (A : Type i) → A ≻ (Lift ⊤) → is-contr A
    ≻-⊤-is-contr A ω = self-orth-is-contr A (ω A (Unit-orth A))

    -- We jump a universe level, but its certainly convenient ...
    is-hyper-prop : Type i → Type (lsucc i)
    is-hyper-prop A = (X Y : Type i) (f : X → Y) → X ≻ A → Y ≻ A → (y : Y) → hfiber f y ≻ A

    hyper-prop-kills-paths : (A : Type i) → is-hyper-prop A → (a₀ a₁ : A) → a₀ == a₁ ≻ A
    hyper-prop-kills-paths A hp a₀ a₁ =
      equiv-≻ (hp (Lift ⊤) A (λ _ → a₀) (≻-trivial A) (≻-reflexive A) a₁)
      (equiv (λ { (lift unit , p) → p }) (λ p → (lift unit , p))
             (λ p → idp) (λ { (lift unit , p) → idp }))

  
