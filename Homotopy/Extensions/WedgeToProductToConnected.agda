{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Connected

module Homotopy.Extensions.WedgeToProductToConnected where
  open import Homotopy.Truncation

  private
    module _ {i j} {D E : Set i} (h : E → D) where

      {-
             k
          E ---> F x
          |    /^
          | ≃ /
          |  / l?
          v /
        (x : D)
      -}

      -- The mapping l and the coherence data.
      extension : (F : D → Set j) (k : ∀ x → F (h x)) → Set (max i j)
      extension F k = Σ (Π D F) (λ l → ∀ x → k x ≡ l (h x))

      -- Specialized J rules.
      module _ where
        -- This is a combination of 2~3 basic rules.
        lemma₁ : ∀ (F : D → Set j) (k : ∀ x → F (h x))
          {l₁ l₂ : ∀ x → F x} (p : l₁ ≡ l₂) (q : ∀ x → k x ≡ l₁ (h x)) a
          → transport (λ l → ∀ x → k x ≡ l (h x)) p q a
          ≡ q a ∘ happly p (h a)
        lemma₁ F k (refl _) q a = ! $ refl-right-unit _

        -- May be generalized later.
        lemma₂ : ∀ {i} {X : Set i} {x₁ x₂ x₃ : X}
          (p₁ : x₁ ≡ x₂) (p₂ : x₂ ≡ x₃) (p₃ : x₁ ≡ x₃)
          → (p₁ ∘ p₂ ≡ p₃) ≡ (p₂ ≡ ! p₁ ∘ p₃)
        lemma₂ (refl _) _ _ = refl _

        -- May be generalized later.
        lemma₃ : ∀ {i} {X : Set i} {x₁ x₂ : X}
          (p₁ : x₁ ≡ x₂) (p₂ : x₁ ≡ x₂)
          → (p₁ ≡ p₂) ≡ (p₂ ≡ p₁)
        lemma₃ p₁ p₂ = eq-to-path $ ! , iso-is-eq ! ! opposite-opposite opposite-opposite

        lemma₄ : ∀ {i j} {A A′ : Set i} (B′ : A′ → Set j) (eq : A ≃ A′)
          → Σ A (λ x → (B′ (eq ☆ x))) ≡ Σ A′ B′
        lemma₄ {j = j} B′ eq = equiv-induction
          (λ {A A′} eq → ∀ (B′ : A′ → Set j) → Σ A (λ x → (B′ (eq ☆ x))) ≡ Σ A′ B′)
          (λ A _ → refl _)
          eq B′

      -- The main lemma
      module _ {n₁ : ℕ₋₂} (h-is-conn : has-connected-fibers n₁ h) where
        extension-is-truncated :
          (F : D → Set j)
          {n₂ : ℕ₋₂} ⦃ F-is-trunc : ∀ x → is-truncated (n₂ +2+ n₁) (F x) ⦄
          (k : ∀ x → F (h x))
          → is-truncated n₂ (extension F k)
        extension-is-truncated F {⟨-2⟩} ⦃ F-is-trunc ⦄ k =
          let
            -- The section
            l′ : ∀ x → τ n₁ (hfiber h x) → F x
            l′ x = τ-extend-nondep ⦃ F-is-trunc x ⦄
              λ{(preimage , shift) → transport F shift (k preimage)}

            -- The section
            l : ∀ x → F x
            l x = l′ x (π₁ (h-is-conn x))

            -- The coherence data (commutivity)
            coh : ∀ x → k x ≡ l (h x)
            coh x = ap (l′ (h x)) $ π₂ (h-is-conn (h x)) $ proj (x , refl _)

            -- The canonical choice of section+coherence
            center : extension F k
            center = l , coh

            -- The path between the canonical choice and others (pointwise).
            path-l-pointwise′ : ∀ (e : extension F k) x → τ n₁ (hfiber h x) → π₁ e x ≡ l x
            path-l-pointwise′ = λ{(l″ , coh″) x →
              τ-extend-nondep
              ⦃ ≡-is-truncated n₁ $ F-is-trunc x ⦄
              -- The point is to make all artifacts go away when shift = refl _.
              (λ{(pre , shift) → transport (λ x → l″ x ≡ l x) shift $
                l″ (h pre)
                  ≡⟨ ! $ coh″ pre ⟩
                k pre
                  ≡⟨ coh pre ⟩∎
                l (h pre)
                  ∎})}

            -- The path between the canonical choice and others (pointwise).
            path-l-pointwise : ∀ (e : extension F k) x → π₁ e x ≡ l x
            path-l-pointwise = λ e x →
              path-l-pointwise′ e x (π₁ (h-is-conn x))

            -- The path between the canonical choice and others.
            path-l : ∀ (e : extension F k) → π₁ e ≡ l
            path-l = funext ◯ path-l-pointwise

            -- The path between the canonical choice and others.
            path-coh : ∀ (e : extension F k)
              → transport (λ l → ∀ x → k x ≡ l (h x)) (path-l e) (π₂ e)
              ≡ coh
            path-coh e″ = funext λ x → let coh″ = π₂ e″ in
              transport (λ l → ∀ x → k x ≡ l (h x)) (path-l e″) coh″ x
                ≡⟨ lemma₁ F k (path-l e″) coh″ x ⟩
              coh″ x ∘ happly (path-l e″) (h x)
                ≡⟨ ap (λ p → coh″ x ∘ p (h x)) $ happly-funext (path-l-pointwise e″) ⟩
              coh″ x ∘ (path-l-pointwise′ e″ (h x) (π₁ (h-is-conn (h x))))
                ≡⟨ ap (λ y → π₂ e″ x ∘ (path-l-pointwise′ e″ (h x) y))
                      $ ! $ π₂ (h-is-conn (h x)) $ proj (x , refl _) ⟩
              coh″ x ∘ (path-l-pointwise′ e″ (h x) (proj (x , refl _)))
                ≡⟨ refl _ ⟩
              coh″ x ∘ ((! $ coh″ x) ∘ coh x)
                ≡⟨ ! $ concat-assoc (coh″ x) (! $ coh″ x) (coh x) ⟩
              (coh″ x ∘ (! $ coh″ x)) ∘ coh x
                ≡⟨ ap (λ p → p ∘ coh x) $ opposite-right-inverse (coh″ x) ⟩∎
              coh x
                ∎
          in center , (λ e″ → Σ-eq (path-l e″) (path-coh e″))
        extension-is-truncated F {S n₂} ⦃ F-is-trunc ⦄ k = λ e₁ e₂ →
          let
            (l₁ , coh₁) = e₁
            (l₂ , coh₂) = e₂

            -- The trick: Make a new F for the path space.
            F′ : ∀ D → Set j
            F′ x = l₁ x ≡ l₂ x

            k′ : ∀ x → F′ (h x)
            k′ x = ! (coh₁ x) ∘ coh₂ x

            F′-is-trunc : ∀ x → is-truncated (n₂ +2+ n₁) (F′ x)
            F′-is-trunc x = F-is-trunc x (l₁ x) (l₂ x)

            extension′ : Set (max i j)
            extension′ = extension F′ k′

            -- Conversion between paths and new extensions.
            extension≡-extension′-path : (e₁ ≡ e₂) ≡ extension′
            extension≡-extension′-path =
              e₁ ≡ e₂
                ≡⟨ ! $ eq-to-path $ total-Σ-eq-equiv ⟩
              Σ (l₁ ≡ l₂) (λ l₁≡l₂ → transport (λ l → ∀ x → k x ≡ l (h x)) l₁≡l₂ coh₁ ≡ coh₂)
                ≡⟨ ap (Σ (l₁ ≡ l₂)) (funext λ _ → ! $ eq-to-path $ funext-equiv) ⟩
              Σ (l₁ ≡ l₂) (λ l₁≡l₂ → ∀ x → transport (λ l → ∀ x → k x ≡ l (h x)) l₁≡l₂ coh₁ x ≡ coh₂ x)
                ≡⟨ ap (Σ (l₁ ≡ l₂)) (funext λ l₁≡l₂ → ap (λ p → ∀ x → p x ≡ coh₂ x)
                      $ funext $ lemma₁ F k l₁≡l₂ coh₁) ⟩
              Σ (l₁ ≡ l₂) (λ l₁≡l₂ → ∀ x → coh₁ x ∘ happly l₁≡l₂ (h x) ≡ coh₂ x)
                ≡⟨ ap (Σ (l₁ ≡ l₂)) (funext λ l₁≡l₂ → ap (λ p → ∀ x → p x)
                      $ funext λ x → lemma₂ (coh₁ x) (happly l₁≡l₂ (h x)) (coh₂ x)) ⟩
              Σ (l₁ ≡ l₂) (λ l₁≡l₂ → ∀ x → happly l₁≡l₂ (h x) ≡ ! (coh₁ x) ∘ coh₂ x)
                ≡⟨ ap (Σ (l₁ ≡ l₂)) (funext λ l₁≡l₂ → ap (λ p → ∀ x → p x)
                      $ funext λ x → lemma₃ (happly l₁≡l₂ (h x)) (! (coh₁ x) ∘ coh₂ x)) ⟩
              Σ (l₁ ≡ l₂) (λ l₁≡l₂ → ∀ x → ! (coh₁ x) ∘ coh₂ x ≡ happly l₁≡l₂ (h x))
                ≡⟨ lemma₄ (λ l₁x≡l₂x → ∀ x → ! (coh₁ x) ∘ coh₂ x ≡ l₁x≡l₂x (h x)) happly-equiv ⟩∎
              extension′
                ∎

            -- Recursive calls.
            extension′-is-trunc : is-truncated n₂ extension′
            extension′-is-trunc = extension-is-truncated F′ {n₂} ⦃ F′-is-trunc ⦄ k′

          in transport (is-truncated n₂) (! extension≡-extension′-path) extension′-is-trunc

  -- The main factorization theorem
  module _ {i j : Level} where
    open import Homotopy.Pushout
    open import Homotopy.Wedge

    connected-extend : ∀ (d : wedge-diag i) → let open wedge-diag d in
      ∀ (P : A → B → Set j) {n₁ n₂}
      ⦃ P-is-trunc : ∀ a b → is-truncated (n₁ +2+ n₂) (P a b) ⦄
      (f-is-conn : has-connected-fibers n₁ f)
      (g-is-conn : has-connected-fibers n₂ g)
      (left* : ∀ a c → P a (g c))
      (right* : ∀ b c → P (f c) b)
      (glue* : ∀ c → left* a c ≡ right* b c)
      → (∀ a b → P a b)
    connected-extend d P {n₁} {n₂} ⦃ P-is-trunc ⦄ f-is-conn g-is-conn left* right* glue* =
      extend-magic₃
        where
          open wedge-diag d

          -- The first part: The extension for a fixed [a] is n₁-truncated.
          extension₁ : ∀ a₂ → Set (max i j)
          extension₁ a₂ = extension g (P a₂) (left* a₂)

          extend-magic₁ : ∀ a₂ → is-truncated n₁ (extension₁ a₂)
          extend-magic₁ a₂ = extension-is-truncated
            g g-is-conn (P a₂) ⦃ P-is-trunc a₂ ⦄ (left* a₂)

          -- The second part: The extension of extensions is contractible.
          extension₂ : Set (max i j)
          extension₂ = extension f extension₁ $
            (λ c → (λ b → right* b c) , glue*)

          extend-magic₂ : is-truncated ⟨-2⟩ extension₂
          extend-magic₂ = extension-is-truncated
            f f-is-conn extension₁ ⦃ extend-magic₁ ⦄
            (λ c → (λ b → right* b c) , glue*)

          -- Get the buried function.
          extend-magic₃ : ∀ a b → P a b
          extend-magic₃ a b = π₁ (π₁ (π₁ extend-magic₂) a) b
