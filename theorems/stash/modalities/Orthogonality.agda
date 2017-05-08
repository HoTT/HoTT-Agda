{-# OPTIONS --without-K --rewriting #-}

open import HoTT

open import stash.modalities.JoinAdj

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
  
    Δ : (X A : Type i) → X → (A → X)
    Δ X A = cst

    -- Δ-ap : {X A : Type i} {x y : X} (φ : A → x == y) (a : A)
    --   → λ= φ == ap cst (φ a)
    -- Δ-ap φ a = equiv-is-inj {f = app=} (snd app=-equiv) (λ= φ) (ap cst (φ a)) (λ= (λ a₀ → app=-β φ a₀ ∙ {!lem a₀!}))

    --   where lem : ∀ a₀ → φ a₀ == app= (ap cst (φ a₀)) a₀ 
    --         lem = {!!}

    ⟦_⊥_⟧ : (A : Type i) (X : Type i) → Type i
    ⟦ A ⊥ X ⟧ = is-equiv (Δ X A)

    ctr : {A X : Type i} → ⟦ A ⊥ X ⟧ → (A → X) → X
    ctr A⊥X φ = is-equiv.g A⊥X φ

    ctr-null : {A X : Type i} (A⊥X : ⟦ A ⊥ X ⟧) (φ : A → X)
      → cst (ctr A⊥X φ) == φ 
    ctr-null A⊥X φ = is-equiv.f-g A⊥X φ

    ctr-cst : {A X : Type i} (A⊥X : ⟦ A ⊥ X ⟧) 
      → (x : X) → ctr A⊥X (cst x) == x
    ctr-cst A⊥X x = is-equiv.g-f A⊥X x

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
    orth-emap {A} {B} {X} A⊥ e = is-eq (Δ X B) g f-g g-f

      where g : (B → X) → X
            g φ = ctr A⊥ (φ ∘ (fst e))

            f-g : (φ : B → X) → Δ X B (g φ) == φ
            f-g φ = λ= (λ b → app= (ctr-null A⊥ (φ ∘ (fst e))) (<– e b) ∙ ap φ (<–-inv-r e b) )

            g-f : (x : X) → g (Δ X B x) == x
            g-f x = ctr-cst A⊥ x

    Σ-orth : {A X : Type i} {B : A → Type i} → ⟦ A ⊥ X ⟧ → (B⊥ : (a : A) → ⟦ B a ⊥ X ⟧) → ⟦ Σ A B ⊥ X ⟧
    Σ-orth {A} {X} {B} A⊥ B⊥ = is-eq _ from to-from from-to

      where from : (Σ A B → X) → X
            from φ = ctr A⊥ (λ a → ctr (B⊥ a) (λ b → φ (a , b)))

            to-from : (φ : Σ A B → X) → cst (from φ) == φ
            to-from φ = λ= (λ { (a , b) → app= (ctr-null A⊥ (λ a → ctr (B⊥ a) (λ b → φ (a , b)))) a ∙
                                           app= (ctr-null (B⊥ a) (λ b → φ (a , b))) b })

            from-to : (x : X) → from (cst x) == x
            from-to x = ap (ctr A⊥) (λ= (λ a → ctr-cst (B⊥ a) x)) ∙ ctr-cst A⊥ x

    -- -- This works if the base is connected, but you'll have to add that
    -- fib-orth : {A X : Type i} {B : A → Type i} → ⟦ Σ A B ⊥ X ⟧ →  (a : A) → ⟦ B a ⊥ X ⟧
    -- fib-orth {A} {X} {B} Σ⊥ a = is-eq _ g {!!} {!!}

    --   where g : (φ : B a → X) → X
    --         g φ = ctr Σ⊥ {!!}

    -- -- This looks doomed ...
    -- base-orth : {A X : Type i} {B : A → Type i} → ⟦ Σ A B ⊥ X ⟧ → ⟦ A ⊥ X ⟧
    -- base-orth {A} {X} {B} Σ⊥ = is-eq _ g f-g {!!}

    --   where g : (φ : A → X) → X
    --         g φ = ctr Σ⊥ (uncurry (λ a _ → φ a))

    --         f-g : (φ : A → X) → cst (g φ) == φ
    --         f-g φ = λ= (λ a → app= (ctr-null Σ⊥ (uncurry (λ a _ → φ a))) (a , {!!}))

    ×-orth : {A B X : Type i} → ⟦ A ⊥ X ⟧ → ⟦ B ⊥ X ⟧ → ⟦ A × B ⊥ X ⟧
    ×-orth {B = B} A⊥ B⊥ = Σ-orth {B = λ _ → B} A⊥ (λ _ → B⊥)

    -- Okay, you need to find a simpler way.
    -- *-orth : {A B X : Type i} → ⟦ B ⊥ X ⟧ → ⟦ A * B ⊥ X ⟧
    -- *-orth {A} {B} {X} ω = is-eq (Δ X (A * B)) from to-from from-to

    --   where from : (A * B → X) → X
    --         from f = is-equiv.g ω (f ∘ right)

    --           where test : A → hfiber cst (f ∘ right)
    --                 test =  snd (–> (join-adj A B X) f) 
                    
    --         to-from : (f : A * B → X) → Δ X (A * B) (from f) == f
    --         to-from f = {!!}

    --         from-to : (x : X) → from (Δ X (A * B) x) == x
    --         from-to x = {!is-equiv.g-f ω x!}

    postulate

      -- Right, this is a special case of the join adjunction ...
      adj-orth : (A X : Type i) → ⟦ Susp A ⊥ X ⟧ → (x y : X) → ⟦ A ⊥ x == y ⟧

    pths-orth : {A X : Type i} {x y : X} → ⟦ A ⊥ X ⟧ → ⟦ A ⊥ x == y ⟧
    pths-orth {A} {X} {x} {y} A⊥X = is-eq (Δ (x == y) A) g to-from from-to

      where g : (A → x == y) → x == y
            g φ = ! (ctr-cst A⊥X x) ∙ ap (ctr A⊥X) (λ= φ) ∙ ctr-cst A⊥X y 

            to-from : (φ : A → x == y) → Δ (x == y) A (g φ) == φ
            to-from φ = λ= coh

              where coh : (a : A) → g φ == φ a
                    coh a = ! (ctr-cst A⊥X x) ∙ ap (ctr A⊥X) (λ= φ) ∙ ctr-cst A⊥X y =⟨ {!!} ⟩
                            φ a ∎

                      where puzzle = ap (ctr A⊥X) (λ= φ) =⟨ {!a !} ⟩
                                     ap (ctr A⊥X) (ap cst (φ a)) =⟨ ∘-ap (ctr A⊥X) cst (φ a) ⟩ 
                                     ap ((ctr A⊥X) ∘ cst) (φ a) ∎

                            eq : ctr-cst A⊥X x ∙' φ a == ap ((ctr A⊥X) ∘ cst) (φ a) ∙ ctr-cst A⊥X y
                            eq = ↓-app=idf-out (apd (ctr-cst A⊥X) (φ a))

                            eq₀ : ctr-null A⊥X (cst x) ∙' λ= φ == ap (cst ∘ (ctr A⊥X)) (λ= φ) ∙ ctr-null A⊥X (cst y)
                            eq₀ = ↓-app=idf-out (apd (ctr-null A⊥X) (λ= φ))

                            adj : ap cst (ctr-cst A⊥X x) == ctr-null A⊥X (cst x)
                            adj = is-equiv.adj A⊥X x

                            adj' : ap (ctr A⊥X) (ctr-null A⊥X (cst x)) == ctr-cst A⊥X (ctr A⊥X (cst x))
                            adj' = is-equiv.adj' A⊥X (cst x)

                            claim : (λ= φ) == ! (ap cst (ctr-cst A⊥X x)) ∙ ap cst (ap (ctr A⊥X) (λ= φ)) ∙ ap cst (ctr-cst A⊥X y)
                            claim = {!!}

                            then : (λ= φ) == ap cst (! (ctr-cst A⊥X x) ∙ ap (ctr A⊥X) (λ= φ) ∙ ctr-cst A⊥X y)
                            then = {!!}
                            
            from-to : (p : x == y) → g (cst p) == p
            from-to p = {!!}
            
    -- ctr : {A X : Type i} → ⟦ A ⊥ X ⟧ → (A → X) → X
    -- ctr A⊥X φ = is-equiv.g A⊥X φ

    -- ctr-null : {A X : Type i} (A⊥X : ⟦ A ⊥ X ⟧) (φ : A → X)
    --   → cst (ctr A⊥X φ) == φ 
    -- ctr-null A⊥X φ = is-equiv.f-g A⊥X φ

    -- ctr-cst : {A X : Type i} (A⊥X : ⟦ A ⊥ X ⟧) 
    --   → (x : X) → ctr A⊥X (cst x) == x
    -- ctr-cst A⊥X x = is-equiv.g-f A⊥X x

  -- Weak cellular inequalities
  module _ {i} where
  
    _≻_ : Type i → Type i → Type _
    X ≻ A = (Y : Type i) → ⟦ A ⊥ Y ⟧ → ⟦ X ⊥ Y ⟧

    ≻-emap : {X Y : Type i} {A : Type i} → X ≻ A → X ≃ Y → Y ≻ A
    ≻-emap {X} {Y} {A} ω e Z o = orth-emap (ω Z o) e

    ≻-trivial : (A : Type i) → (Lift ⊤) ≻ A
    ≻-trivial A X _ = Unit-orth X
  
    ≻-reflexive : (A : Type i) → A ≻ A
    ≻-reflexive A Y x = x

    ≻-trans : (A B C : Type i) → A ≻ B → B ≻ C → A ≻ C
    ≻-trans A B C ω₀ ω₁ Y cy = ω₀ Y (ω₁ Y cy)
            
    ≻-⊤-is-contr : (A : Type i) → A ≻ (Lift ⊤) → is-contr A
    ≻-⊤-is-contr A ω = self-orth-is-contr A (ω A (Unit-orth A))

    Σ-≻ : {A X : Type i} {P : X → Type i} → X ≻ A → (P≻A : (x : X) → P x ≻ A) → Σ X P ≻ A
    Σ-≻ X≻A P≻A Y A⊥Y = Σ-orth (X≻A Y A⊥Y) (λ x → P≻A x Y A⊥Y)
    
    -- We jump a universe level, but its certainly convenient ...
    is-hyper-prop : Type i → Type (lsucc i)
    is-hyper-prop A = (X Y : Type i) (f : X → Y) → X ≻ A → Y ≻ A → (y : Y) → hfiber f y ≻ A

    hp-kills-paths : (A : Type i) → is-hyper-prop A
      → (X : Type i) → X ≻ A
      → (x y : X) → (x == y) ≻ A
    hp-kills-paths A hp X X≻A x y = ≻-emap (hp (Lift ⊤) X (λ _ → x) (≻-trivial A) X≻A y)
      (equiv snd (λ p → (_ , p)) (λ _ → idp) (λ _ → idp))

    -- Okay, so in some sense this is much more natural.
    -- It just says the connected guys have to be closed under
    -- diagonals.
    kills-paths-hp : (A : Type i)
      → (κ : (X : Type i) → X ≻ A → (x y : X) → (x == y) ≻ A)
      → is-hyper-prop A
    kills-paths-hp A κ X Y f X≻A Y≻A y = Σ-≻ X≻A (λ x → κ Y Y≻A (f x) y)

    -- You'll have to think a bit about why this is equivalent
    -- to *preserving* the path spaces.

    ×-≻ : {A B X : Type i} → A ≻ X → B ≻ X → A × B ≻ X
    ×-≻ ω₀ ω₁ Y e = ×-orth (ω₀ Y e) (ω₁ Y e)
    
    postulate
      susp-≻ : (A : Type i) → Susp A ≻ A
