{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Connected

module Homotopy.BlakersMassey
  {i} {X Y : Set i} (Q : X → Y → Set i)
  {m} (Q-is-conn-x : ∀ x → is-connected (S m) (Σ Y (λ y → Q x y)))
  {n} (Q-is-conn-y : ∀ y → is-connected (S n) (Σ X (λ x → Q x y)))
  where

  open import Homotopy.PointConnected
  open import Homotopy.Truncation
  open import Homotopy.Extensions.ProductPushoutToProductToConnected
  open import Homotopy.BlakersMassey.PushoutWrapper Q

  open import Homotopy.BlakersMassey.CoherenceData Q Q-is-conn-x Q-is-conn-y

  module _ {x₀} {y₀} (q₀₀ : Q x₀ y₀) where

    -- Step 1:
    -- Generalizing the theorem to [left x ≡ p] for arbitrary p.
    -- This requires a pushout-rec

    code-left : ∀ x → left x₀ ≡ left x → Set i
    code-left _ r = τ (n +2+ m) (hfiber (glue-!glue q₀₀) r)

    code-right : ∀ y → left x₀ ≡ right y → Set i
    code-right _ r = τ (n +2+ m) (hfiber glue r)

    -- This template is useful in simplifying the equality proof.
    -- The trick is to keep a₁ and a₂ free so that we can plug in
    -- refl whenever we feel like it.
    code-glue-template : ∀ {i j} {A : Set i} {P : Set j}
      {a₀ a₁ : A} (P₁ : a₀ ≡ a₁ → P) {a₂} (P₂ : a₀ ≡ a₂ → P)
      (a₁≡a₂ : a₁ ≡ a₂) (r : a₀ ≡ a₂)
      → P₁ (r ∘ ! a₁≡a₂) ≡ P₂ r
      → transport (λ p → a₀ ≡ p → P) a₁≡a₂ P₁ r ≡ P₂ r
    code-glue-template {P = P} {a₀} P₁ P₂ a₁≡a₂ r lemma =
      transport (λ p → a₀ ≡ p → P) a₁≡a₂ P₁ r
          ≡⟨ trans-app→cst (λ p → a₀ ≡ p) a₁≡a₂ P₁ r ⟩
      P₁ (transport (λ p → a₀ ≡ p) (! a₁≡a₂) r)
          ≡⟨ ap P₁ $ trans-cst≡id (! a₁≡a₂) r ⟩
      P₁ (r ∘ ! a₁≡a₂)
          ≡⟨ lemma ⟩
      P₂ r
          ∎

    -- The real glue, that is, the template with the [cross] magic.
    code-glue : ∀ {x₁} {y₁} (q₁₁ : Q x₁ y₁) (r : left x₀ ≡ right y₁)
      → transport (λ p → left x₀ ≡ p → Set i) (glue q₁₁) (code-left x₁) r
      ≡ code-right y₁ r
    code-glue {x₁} {y₁} q₁₁ r =
      code-glue-template (code-left x₁) (code-right y₁) (glue q₁₁) r
        (! $ cross-path q₀₀ q₁₁ r)

    -- Here's the data structure for the generalized theorem.
    -- Note that the pushout P here is not the general pushout.
    code : ∀ p → left x₀ ≡ p → Set i
    code = pushout-rec
      (λ p → left x₀ ≡ p → Set i)
      code-left
      code-right
      (funext ◯ code-glue)

    -- Step 2:
    -- [code] is contractible!

    -- The center for refl.  We will use transport to find the center
    -- in other fibers.
    code-center-refl : code (left x₀) refl
    code-center-refl = proj $ q₀₀ , opposite-right-inverse (glue q₀₀)

    -- This is the breakdown of the path for coercing:
    --   (ap2 f r₂ (trans-cst≡id r₂ refl))
    -- We will need the broken-down version anyway,
    -- so why not breaking them down from the very beginning?

    -- The template here, again, is to keep the possibility
    -- of plugging in [refl] for [a₀≡a₁].
    coerce-path-template : ∀ {i j} {A : Set i} {P : Set j}
      {a₀ : A} (f : (x : A) → a₀ ≡ x → P) {a₁} (a₀≡a₁ : a₀ ≡ a₁)
      → transport (λ x → a₀ ≡ x → P) a₀≡a₁ (f a₀) ≡ f a₁
      → f a₀ refl ≡ f a₁ a₀≡a₁
    coerce-path-template {P = P} {a₀} f {a₁} a₀≡a₁ lemma =
      f a₀ refl
          ≡⟨ ! $ happly (trans-opposite-trans (λ x → a₀ ≡ x → P) a₀≡a₁ (f a₀)) refl ⟩
      transport (λ x → a₀ ≡ x → P) (! a₀≡a₁)
        (transport (λ x → a₀ ≡ x → P) a₀≡a₁ (f a₀)) refl
          ≡⟨ happly (ap (transport (λ x → a₀ ≡ x → P) (! a₀≡a₁)) lemma) refl ⟩
      transport (λ x → a₀ ≡ x → P) (! a₀≡a₁) (f a₁) refl
          ≡⟨ trans!-app→cst (λ x → a₀ ≡ x) a₀≡a₁ (f a₁) refl ⟩
      f a₁ (transport (λ x → a₀ ≡ x) a₀≡a₁ refl)
          ≡⟨ ap (f a₁) $ trans-cst≡id a₀≡a₁ refl ⟩
      f a₁ a₀≡a₁
          ∎

    -- The real path.
    coerce-path : ∀ {i j} {A : Set i} {P : Set j}
      {a₀ : A} (f : (x : A) → a₀ ≡ x → P) {a₁} (a₀≡a₁ : a₀ ≡ a₁)
      → f a₀ refl ≡ f a₁ a₀≡a₁
    coerce-path f r = coerce-path-template f r (apd f r)

    -- Here shows the use of two templates.  It will be super painful
    -- if we cannot throw in [refl].  Now we only have to deal with
    -- simple computations.
    abstract
      coerce-path-code-glue-template : ∀ {i j} {A : Set i} {P : Set j}
        {a₀ : A} (f : (x : A) → a₀ ≡ x → P) {a₁} (a₀≡a₁ : a₀ ≡ a₁)
        (lemma : ∀ r → f a₀ (r ∘ ! a₀≡a₁) ≡ f a₁ r)
        → coerce-path-template f a₀≡a₁
            (funext λ r → code-glue-template (f a₀) (f a₁) a₀≡a₁ r (lemma r))
        ≡ ap (f a₀) (! $ opposite-right-inverse a₀≡a₁) ∘ lemma a₀≡a₁
      coerce-path-code-glue-template {a₀ = a₀} f refl lemma =
        happly (ap (id _)
            (funext λ r → ap (f (a₀)) (! $ refl-right-unit r) ∘ lemma r ∘ refl)) refl ∘ refl
          ≡⟨ ap (λ p → happly p refl ∘ refl) $ ap-id
                $ (funext λ r → ap (f (a₀)) (! $ refl-right-unit r) ∘ lemma r ∘ refl) ⟩
        happly (funext λ r → ap (f (a₀)) (! $ refl-right-unit r) ∘ lemma r ∘ refl) refl ∘ refl
          ≡⟨ ap (λ p → p refl ∘ refl) $ happly-funext
                $ (λ r → ap (f (a₀)) (! $ refl-right-unit r) ∘ lemma r ∘ refl) ⟩
        (lemma refl ∘ refl) ∘ refl -- The trailing [refl]'s are annoying.
          ≡⟨ refl-right-unit $ lemma refl ∘ refl ⟩
        lemma refl ∘ refl
          ≡⟨ refl-right-unit $ lemma refl ⟩
        lemma refl
          ∎

    -- Here is the actually lemma we want!
    -- A succinct breakdown of [coerce-path code (glue q)].
    abstract
      coerce-path-code-glue : ∀ {y} (q : Q x₀ y)
        → coerce-path code (glue q)
        ≡ ap (τ (n +2+ m) ◯ hfiber (glue-!glue q₀₀)) (! $ opposite-right-inverse $ glue q)
        ∘ (! $ cross-path q₀₀ q (glue q))
      coerce-path-code-glue q =
        coerce-path-template code (glue q) (apd code (glue q))
            ≡⟨ ap (coerce-path-template code (glue q))
                  $ pushout-β-glue
                      (λ p → left x₀ ≡ p → Set i)
                      code-left
                      code-right
                      (funext ◯ code-glue)
                      q ⟩
        coerce-path-template code (glue q) (funext $ code-glue q)
            ≡⟨ coerce-path-code-glue-template code (glue q)
                (λ r → ! $ cross-path q₀₀ q r) ⟩
        ap (code-left _) (! $ opposite-right-inverse $ glue q)
          ∘ (! $ cross-path q₀₀ q (glue q))
            ∎

    -- Find the center in other fibers.
    code-transport : ∀ {p} r → code _ refl → code p r
    code-transport r = transport (id _) (coerce-path code r)
    code-center : ∀ {p} r → code p r
    code-center r = code-transport r code-center-refl
        
    private
      -- An ugly lemma for this development only.
      trans-τ-hfiber : ∀ {i j} {P : Set i} {Q : Set j}
        {n} (f : P → Q) {q₁ q₂ : Q} (p : q₁ ≡ q₂) (x : P) (coh : f x ≡ q₁)
        → transport (τ n ◯ hfiber f) p (proj (x , coh))
        ≡ proj (x , (coh ∘ p))
      trans-τ-hfiber f refl x refl = refl

    -- This is the only case you care for contractibiltiy.
    abstract
      code-coh-lemma : ∀ {y} (q : Q x₀ y) → code-center (glue q) ≡ proj (q , refl)
      code-coh-lemma q =
        transport (id _) (coerce-path code (glue q)) code-center-refl
              ≡⟨ ap (λ p → transport (id _) p code-center-refl) $ coerce-path-code-glue q ⟩
        transport (id _)
          ( ap (τ (n +2+ m) ◯ hfiber (glue-!glue q₀₀)) (! $ opposite-right-inverse $ glue q)
            ∘ (! $ cross-path q₀₀ q (glue q)))
          code-center-refl
              ≡⟨ trans-concat
                  (id _)
                  (! $ cross-path q₀₀ q (glue q))
                  (ap (code-left _) (! $ opposite-right-inverse $ glue q))
                  code-center-refl ⟩
        transport (id _)
          (! $ cross-path q₀₀ q (glue q))
          (transport (id _)
            (ap (code-left _) (! $ opposite-right-inverse $ glue q))
            code-center-refl)
              ≡⟨ ap (transport (id _) (! $ cross-path q₀₀ q (glue q)))
                    $ trans-ap (id _) (code-left _) (! $ opposite-right-inverse $ glue q)
                      code-center-refl ⟩
        transport (id _)
          (! $ cross-path q₀₀ q (glue q))
          (transport (code-left _) (! $ opposite-right-inverse $ glue q)
            code-center-refl)
              ≡⟨ ap (transport (id _) (! $ cross-path q₀₀ q (glue q)))
                    $ trans-τ-hfiber
                        (glue-!glue q₀₀)
                        (! $ opposite-right-inverse $ glue q)
                        q₀₀
                        (opposite-right-inverse (glue q₀₀)) ⟩
        transport (id _)
          (! $ cross-path q₀₀ q (glue q))
          (proj (q₀₀ , glue-!glue-path q₀₀ q))
              ≡⟨ trans-id-!eq-to-path (cross-equiv q₀₀ q (glue q)) _ ⟩
        inverse (cross-equiv q₀₀ q (glue q))
          (proj (q₀₀ , glue-!glue-path q₀₀ q))
              ≡⟨ ap (λ p → inverse (cross-equiv q₀₀ q (glue q)) (proj (q₀₀ , p)))
                    $ ! $ refl-right-unit $ glue-!glue-path q₀₀ q ⟩
        inverse (cross-equiv q₀₀ q (glue q))
          (proj (q₀₀ , (glue-!glue-path q₀₀ q ∘ refl)))
              ≡⟨ ap (λ p → inverse (cross-equiv q₀₀ q (glue q))
                        (proj (q₀₀ , (glue-!glue-path q₀₀ q ∘ p))))
                    $ ! $ whisker-right-refl (! (glue q)) {glue q} ⟩
        inverse (cross-equiv q₀₀ q (glue q))
          (proj (q₀₀ , (glue-!glue-path q₀₀ q ∘ whisker-right (! (glue q)) {glue q} refl )))
              ≡⟨ move-inverse (cross-equiv q₀₀ q (glue q)) $ cross′-β-right q₀₀ q (glue q) refl ⟩
        proj (q , refl)
              ∎

    -- Make [r] free to use J.
    code-coh : ∀ {y} (r : left x₀ ≡ right y) (s : hfiber glue r) → proj s ≡ code-center r
    code-coh ._ (q , refl) = ! $ code-coh-lemma q

    -- Finish the lemma.
    code-contr : ∀ {y} (r : left x₀ ≡ right y) → is-contr (code _ r)
    code-contr r = code-center r , τ-extend
      ⦃ λ _ → ≡-is-truncated (n +2+ m) $ τ-is-truncated (n +2+ m) _ ⦄
      (code-coh r)

  -- The final theorem.
  -- It is sufficient to find some [q₀₀].
  blaker-massey : ∀ {x₀} {y₀} (r : left x₀ ≡ right y₀) → is-connected (n +2+ m) (hfiber glue r)
  blaker-massey {x₀} r = τ-extend-nondep
    ⦃ prop-is-truncated-S m $ is-connected-is-prop (n +2+ m) ⦄
    (λ{(_ , q₀₀) → code-contr q₀₀ r})
    (π₁ (Q-is-conn-x x₀))

