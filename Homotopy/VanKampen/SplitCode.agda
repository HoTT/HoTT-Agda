{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.PushoutDef
open import Homotopy.VanKampen.Guide

module Homotopy.VanKampen.SplitCode {i} (d : pushout-diag i)
  (l : legend i (pushout-diag.C d)) (a₁ : pushout-diag.A d) where

  open pushout-diag d
  open legend l

  open import Homotopy.Truncation
  open import Homotopy.PathTruncation

  -- Definition.
  module _ where
    private
      data #code-a (a₂ : A) : Set i
      data #code-b (b₂ : B) : Set i

      data #code-a a₂ where
        #a : a₁ ≡₀ a₂ → #code-a a₂
        #ba : ∀ n → #code-b (g $ loc n) → f (loc n) ≡₀ a₂ → #code-a a₂
      data #code-b b₂ where
        #ab : ∀ n → #code-a (f $ loc n) → g (loc n) ≡₀ b₂ → #code-b b₂

    code-b : B → Set i
    code-b = #code-b

    code-a : A → Set i
    code-a = #code-a

    postulate -- HIT
      code-a-is-set : ∀ a → is-set (code-a a)
      code-b-is-set : ∀ b → is-set (code-b b)

    a : ∀ {a₂} → a₁ ≡₀ a₂ → code-a a₂
    a = #a

    infixl 6 a
    syntax a co = ⟧a co

    ba : ∀ {a₂} n → code-b (g $ loc n) → f (loc n) ≡₀ a₂ → code-a a₂
    ba = #ba

    infixl 6 ba
    syntax ba n co p = co b⟦ n ⟧a p

    ab : ∀ {b₂} n → code-a (f $ loc n) → g (loc n) ≡₀ b₂ → code-b b₂
    ab = #ab

    infixl 6 ab
    syntax ab n co p = co a⟦ n ⟧b p

    postulate -- HIT
      code-a-refl-refl : ∀ n (co : code-a (f $ loc n))
        → co a⟦ n ⟧b refl₀ b⟦ n ⟧a refl₀ ≡ co
      code-b-refl-refl : ∀ n (co : code-b (g $ loc n))
        → co b⟦ n ⟧a refl₀ a⟦ n ⟧b refl₀ ≡ co
      -- The other diriction is fine.
      -- There's no canonical choice between two, I think.
      code-ab-swap : ∀ n₁ co n₂ (r : loc n₁ ≡₀ loc n₂)
        → co a⟦ n₁ ⟧b ap₀ g r b⟦ n₂ ⟧a refl₀
        ≡ co a⟦ n₁ ⟧b refl₀ b⟦ n₁ ⟧a ap₀ f r

    -- Dependent recursor.
    code-rec : ∀ {j}
      (P-a : ∀ {a₂} → code-a a₂ → Set j) ⦃ _ : ∀ {a₂} co → is-set $ P-a {a₂} co ⦄
      (P-b : ∀ {b₂} → code-b b₂ → Set j) ⦃ _ : ∀ {b₂} co → is-set $ P-b {b₂} co ⦄
      (h₀-a : ∀ {a₂} (p : _ ≡₀ a₂) → P-a (a p))
      (h₀-ba : ∀ {a₂} n {co} (_ : P-b co) (p : _ ≡₀ a₂)
        → P-a (co b⟦ n ⟧a p))
      (h₀-ab : ∀ {b₂} n {co} (_ : P-a co) (p : _ ≡₀ b₂)
        → P-b (co a⟦ n ⟧b p))
      (h₁-a-rr : ∀ n {co} (pco : P-a co) →
        transport (P-a {f $ loc n}) (code-a-refl-refl n co)
          (h₀-ba n (h₀-ab n pco $ refl₀) $ refl₀)
        ≡ pco)
      (h₁-b-rr : ∀ n {co} (pco : P-b co) →
        transport (P-b {g $ loc n}) (code-b-refl-refl n co)
          (h₀-ab n (h₀-ba n pco $ refl₀) $ refl₀)
        ≡ pco)
      (h₁-ab-s : ∀ n₁ {co} (pco : P-a co) n₂ r →
        transport (P-a {f $ loc n₂}) (code-ab-swap n₁ co n₂ r)
          (h₀-ba n₂ (h₀-ab n₁ pco $ ap₀ g r) $ refl₀)
        ≡ (h₀-ba n₁ (h₀-ab n₁ pco $ refl₀) $ ap₀ f r))
      → (∀ {a₂} (co : code-a a₂) → P-a co)
      × (∀ {b₂} (co : code-b b₂) → P-b co)
    code-rec P-a P-b h₀-a h₀-ba h₀-ab _ _ _ = elim-a , elim-b
      where
        elim-a : ∀ {a₂} (co : code-a a₂) → P-a co
        elim-b : ∀ {b₂} (co : code-b b₂) → P-b co
        elim-a (#a       p) = h₀-a                p
        elim-a (#ba n co p) = h₀-ba n (elim-b co) p
        elim-b (#ab n co p) = h₀-ab n (elim-a co) p

    -- This is actually "partially dependent".
    -- P-a and P-b are indexed by the end points.
    -- This is fine because they are fixed in
    -- all transports in 1-cells.
    code-rec-nondep : ∀ {j}
      (P-a : A → Set j) ⦃ _ : ∀ a → is-set $ P-a a ⦄
      (P-b : B → Set j) ⦃ _ : ∀ b → is-set $ P-b b ⦄
      (h₀-a : ∀ {a₂} (p : a₁ ≡₀ a₂) → P-a a₂)
      (h₀-ba : ∀ {a₂} n {co : code-b (g $ loc n)} → P-b (g $ loc n)
        → f (loc n) ≡₀ a₂ → P-a a₂)
      (h₀-ab : ∀ {b₂} n {co : code-a (f $ loc n)} → P-a (f $ loc n)
        → g (loc n) ≡₀ b₂ → P-b b₂)
      (h₁-a-rr : ∀ n {co} (pco : P-a (f $ loc n))
        → h₀-ba n {co a⟦ n ⟧b refl₀} (h₀-ab n {co} pco $ refl₀) refl₀ ≡ pco)
      (h₁-b-rr : ∀ n {co} (pco : P-b (g $ loc n))
        → h₀-ab n {co b⟦ n ⟧a refl₀} (h₀-ba n {co} pco $ refl₀) refl₀ ≡ pco)
      (h₁-ab-s : ∀ n₁ {co : code-a $ f $ loc n₁} (pco : P-a $ f $ loc n₁) n₂ (r : loc n₁ ≡₀ loc n₂) →
          h₀-ba n₂ {co a⟦ n₁ ⟧b ap₀ g r} (h₀-ab n₁ {co} pco $ ap₀ g r) refl₀
        ≡ h₀-ba n₁ {co a⟦ n₁ ⟧b refl₀} (h₀-ab n₁ {co} pco $ refl₀) (ap₀ f r))
      → (∀ {a₂} (co : code-a a₂) → P-a a₂)
      × (∀ {b₂} (co : code-b b₂) → P-b b₂)
    code-rec-nondep P-a P-b h₀-a h₀-ba h₀-ab _ _ _ = elim-a , elim-b
      where
        elim-a : ∀ {a₂} (co : code-a a₂) → P-a a₂
        elim-b : ∀ {b₂} (co : code-b b₂) → P-b b₂
        elim-a (#a       p) = h₀-a                     p
        elim-a (#ba c co p) = h₀-ba c {co} (elim-b co) p
        elim-b (#ab c co p) = h₀-ab c {co} (elim-a co) p

  module _ where
    trans-a : ∀ {y z} (q : y ≡ z) (p : a₁ ≡₀ y)
      → transport code-a q (⟧a p) ≡ ⟧a (p ∘₀ proj q)
    trans-a refl p = ap a (! (refl₀-right-unit p))

    trans-ba : ∀ {y z} (q : y ≡ z) n co (p : f (loc n) ≡₀ y)
      → transport code-a q (co b⟦ n ⟧a p) ≡ co b⟦ n ⟧a p ∘₀ proj q
    trans-ba refl n co p = ap (ba n co) (! (refl₀-right-unit p))

    trans-ab : ∀ {y b} (q : y ≡ b) n co (p : g (loc n) ≡₀ y)
      → transport code-b q (co a⟦ n ⟧b p) ≡ co a⟦ n ⟧b p ∘₀ proj q
    trans-ab refl n co p = ap (ab n co) (! (refl₀-right-unit p))

  module _ where
    -- all-paths
    abstract
      code-has-all-cells₂-a : ∀ {a} {x y : code-a a} (p q : x ≡ y) → p ≡ q
      code-has-all-cells₂-a = prop-has-all-paths $ code-a-is-set _ _ _

      code-has-all-cells₂-b : ∀ {b} {x y : code-b b} (p q : x ≡ y) → p ≡ q
      code-has-all-cells₂-b = prop-has-all-paths $ code-b-is-set _ _ _

    code-a-rec : ∀ {j}
      (P-a : ∀ {a₂} → code-a a₂ → Set j) ⦃ _ : ∀ {a₂} co → is-set $ P-a {a₂} co ⦄
      (h₀-a : ∀ {a₂} (p : _ ≡₀ a₂) → P-a (⟧a p))
      (h₀-ba : ∀ {a₂} n co (p : _ ≡₀ a₂)
        → P-a (co b⟦ n ⟧a p))
      (h₁-a-rr : ∀ n {co} (pco : P-a co) →
        transport (P-a {f $ loc n}) (code-a-refl-refl n co)
          (h₀-ba n (co a⟦ n ⟧b refl₀) $ refl₀)
        ≡ pco)
      → (∀ {a₂} (co : code-a a₂) → P-a co)
    code-a-rec {j} P-a ⦃ P-a-is-set ⦄ h₀-a h₀-ba h₁-a-rr = π₁ $ code-rec
      P-a ⦃ P-a-is-set ⦄
      (λ _ → unit) ⦃ λ _ → unit-is-set ⦄
      h₀-a
      (λ n {co} _ p → h₀-ba n co p)
      (λ _ _ _ → tt)
      h₁-a-rr
      (λ _ _ → prop-has-all-paths unit-is-prop _ _)
      -- FIXME This proof is too ugly.
      (λ n₁ {co} (pco : P-a co) n₂ r →
        transport (P-a {f $ loc n₂}) (code-ab-swap n₁ co n₂ r)
          (h₀-ba n₂ (co a⟦ n₁ ⟧b ap₀ g r) $ refl₀)
            ≡⟨ ! $ h₁-a-rr n₂ _ ⟩
        transport (P-a {f $ loc n₂}) (code-a-refl-refl n₂ _)
          (h₀-ba n₂ (_ a⟦ n₂ ⟧b refl₀) $ refl₀)
            ≡⟨ ap (λ x → transport (P-a {f $ loc n₂}) (code-a-refl-refl n₂ _)
                $ h₀-ba n₂ (_ a⟦ n₂ ⟧b refl₀) $ refl₀) $ code-ab-swap n₁ co n₂ r ⟩
        transport (P-a {f $ loc n₂}) (code-a-refl-refl n₂ _)
          (h₀-ba n₂ (_ a⟦ n₂ ⟧b refl₀) $ refl₀)
            ≡⟨ h₁-a-rr n₂ _ ⟩∎
        h₀-ba n₁ (co a⟦ n₁ ⟧b refl₀) (ap₀ f r)
            ∎)

    code-b-rec : ∀ {j}
      (P-b : ∀ {b₂} → code-b b₂ → Set j) ⦃ _ : ∀ {b₂} co → is-set $ P-b {b₂} co ⦄
      (h₀-ab : ∀ {b₂} n co (p : _ ≡₀ b₂)
        → P-b (co a⟦ n ⟧b p))
      (h₁-b-rr : ∀ n {co} (pco : P-b co) →
        transport (P-b {g $ loc n}) (code-b-refl-refl n co)
          (h₀-ab n (co b⟦ n ⟧a refl₀) $ refl₀)
        ≡ pco)
      → (∀ {b₂} (co : code-b b₂) → P-b co)
    code-b-rec {j} P-b ⦃ P-b-is-set ⦄ h₀-ab h₁-b-rr = π₂ $ code-rec
      (λ _ → unit) ⦃ λ _ → unit-is-set ⦄
      P-b ⦃ P-b-is-set ⦄
      (λ _ → tt)
      (λ _ _ _ → tt)
      (λ n {co} _ p → h₀-ab n co p)
      (λ _ _ → prop-has-all-paths unit-is-prop _ _)
      h₁-b-rr
      (λ _ _ _ _ → prop-has-all-paths unit-is-prop _ _)

  -- Derived 1-cells.
  module _ where
    abstract
      code-ba-swap : ∀ n₁ co n₂ (r : loc n₁ ≡₀ loc n₂)
        → co b⟦ n₁ ⟧a ap₀ f r a⟦ n₂ ⟧b refl₀
        ≡ co b⟦ n₁ ⟧a refl₀ a⟦ n₁ ⟧b ap₀ g r
      code-ba-swap n₁ co n₂ r =
        co                                   b⟦ n₁ ⟧a ap₀ f r a⟦ n₂ ⟧b refl₀
          ≡⟨ ap (λ x → x b⟦ n₁ ⟧a ap₀ f r a⟦ n₂ ⟧b refl₀) $ ! $ code-b-refl-refl n₁ co ⟩
        co b⟦ n₁ ⟧a refl₀ a⟦ n₁ ⟧b refl₀ b⟦ n₁ ⟧a ap₀ f r a⟦ n₂ ⟧b refl₀
          ≡⟨ ap (λ x → x a⟦ n₂ ⟧b refl₀) $ ! $ code-ab-swap n₁ (co b⟦ n₁ ⟧a refl₀) n₂ r ⟩
        co b⟦ n₁ ⟧a refl₀ a⟦ n₁ ⟧b ap₀ g r b⟦ n₂ ⟧a refl₀ a⟦ n₂ ⟧b refl₀
          ≡⟨ code-b-refl-refl n₂ $ co b⟦ n₁ ⟧a refl₀ a⟦ n₁ ⟧b ap₀ g r ⟩∎
        co b⟦ n₁ ⟧a refl₀ a⟦ n₁ ⟧b ap₀ g r
          ∎

    abstract
      -- Old (provable) rules.
      code-a-merge : ∀ {a₂} n p₁ (p₂ : _ ≡₀ a₂)
        → ⟧a p₁ a⟦ n ⟧b refl₀ b⟦ n ⟧a p₂
        ≡ ⟧a p₁            ∘₀           p₂
      code-a-merge {a₂} n p₁ = π₀-extend
        ⦃ λ _ → ≡-is-set $ code-a-is-set a₂ ⦄
        ( λ p₂ →
            ⟧a p₁ a⟦ n ⟧b refl₀ b⟦ n ⟧a proj p₂
              ≡⟨ ! $ trans-ba p₂ n (⟧a p₁ a⟦ n ⟧b refl₀) refl₀ ⟩
            transport code-a p₂ (⟧a p₁ a⟦ n ⟧b refl₀ b⟦ n ⟧a refl₀)
              ≡⟨ ap (transport code-a p₂) $ code-a-refl-refl n (⟧a p₁) ⟩
            transport code-a p₂ (⟧a p₁)
              ≡⟨ trans-a p₂ p₁ ⟩∎
            ⟧a p₁ ∘₀ proj p₂
              ∎)

    abstract
      code-ab-merge : ∀ {b₂} n₁ co n₂ p₁ (p₂ : _ ≡₀ b₂)
        → co a⟦ n₁ ⟧b p₁ b⟦ n₂ ⟧a refl₀ a⟦ n₂ ⟧b p₂
        ≡ co a⟦ n₁ ⟧b p₁             ∘₀            p₂
      code-ab-merge {b₂} n₁ co n₂ p₁ = π₀-extend
        ⦃ λ _ → ≡-is-set $ code-b-is-set b₂ ⦄
        ( λ p₂ →
            co a⟦ n₁ ⟧b p₁ b⟦ n₂ ⟧a refl₀ a⟦ n₂ ⟧b proj p₂
              ≡⟨ ! $ trans-ab p₂ n₂ (co a⟦ n₁ ⟧b p₁ b⟦ n₂ ⟧a refl₀) refl₀ ⟩
            transport code-b p₂ (co a⟦ n₁ ⟧b p₁ b⟦ n₂ ⟧a refl₀ a⟦ n₂ ⟧b refl₀)
              ≡⟨ ap (transport code-b p₂) $ code-b-refl-refl n₂ (co a⟦ n₁ ⟧b p₁) ⟩
            transport code-b p₂ (co a⟦ n₁ ⟧b p₁)
              ≡⟨ trans-ab p₂ n₁ co p₁ ⟩∎
            co a⟦ n₁ ⟧b p₁ ∘₀ proj p₂
              ∎)

    abstract
      code-ba-merge : ∀ {a₂} n₁ co n₂ p₁ (p₂ : _ ≡₀ a₂)
        → co b⟦ n₁ ⟧a p₁ a⟦ n₂ ⟧b refl₀ b⟦ n₂ ⟧a p₂
        ≡ co b⟦ n₁ ⟧a p₁             ∘₀            p₂
      code-ba-merge {a₂} n₁ co n₂ p₁ = π₀-extend
        ⦃ λ _ → ≡-is-set $ code-a-is-set a₂ ⦄
        ( λ p₂ →
            co b⟦ n₁ ⟧a p₁ a⟦ n₂ ⟧b refl₀ b⟦ n₂ ⟧a proj p₂
              ≡⟨ ! $ trans-ba p₂ n₂ (co b⟦ n₁ ⟧a p₁ a⟦ n₂ ⟧b refl₀) refl₀ ⟩
            transport code-a p₂ (co b⟦ n₁ ⟧a p₁ a⟦ n₂ ⟧b refl₀ b⟦ n₂ ⟧a refl₀)
              ≡⟨ ap (transport code-a p₂) $ code-a-refl-refl n₂ (co b⟦ n₁ ⟧a p₁) ⟩
            transport code-a p₂ (co b⟦ n₁ ⟧a p₁)
              ≡⟨ trans-ba p₂ n₁ co p₁ ⟩∎
            co b⟦ n₁ ⟧a p₁ ∘₀ proj p₂
              ∎)

    abstract
      code-a-shift : ∀ {b₂} n₁ p₁ n₂ (r : loc n₁ ≡₀ loc n₂) (p₂ : _ ≡₀ b₂)
        → ⟧a p₁ ∘₀ ap₀ f r a⟦ n₂ ⟧b            p₂
        ≡ ⟧a p₁            a⟦ n₁ ⟧b ap₀ g r ∘₀ p₂
      code-a-shift n₁ p₁ n₂ r p₂ =
        ⟧a p₁             ∘₀            ap₀ f r a⟦ n₂ ⟧b p₂
          ≡⟨ ap (λ x → x a⟦ n₂ ⟧b p₂) $ ! $ code-a-merge n₁ p₁ (ap₀ f r) ⟩
        ⟧a p₁ a⟦ n₁ ⟧b refl₀ b⟦ n₁ ⟧a ap₀ f r a⟦ n₂ ⟧b p₂
          ≡⟨ ap (λ x → x a⟦ n₂ ⟧b p₂) $ ! $ code-ab-swap n₁ (⟧a p₁) n₂ r ⟩
        ⟧a p₁ a⟦ n₁ ⟧b ap₀ g r b⟦ n₂ ⟧a refl₀ a⟦ n₂ ⟧b p₂
          ≡⟨ code-ab-merge n₁ (⟧a p₁) n₂ (ap₀ g r) p₂ ⟩∎
        ⟧a p₁ a⟦ n₁ ⟧b ap₀ g r             ∘₀            p₂
          ∎

    abstract
      code-ba-shift : ∀ {b₂} n₁ co n₂ p₁ n₃ (r : loc n₂ ≡₀ loc n₃) (p₂ : _ ≡₀ b₂)
        → co b⟦ n₁ ⟧a p₁ ∘₀ ap₀ f r a⟦ n₃ ⟧b            p₂
        ≡ co b⟦ n₁ ⟧a p₁            a⟦ n₂ ⟧b ap₀ g r ∘₀ p₂
      code-ba-shift n₁ co n₂ p₁ n₃ r p₂ =
        co b⟦ n₁ ⟧a p₁             ∘₀            ap₀ f r a⟦ n₃ ⟧b p₂
          ≡⟨ ap (λ x → x a⟦ n₃ ⟧b p₂) $ ! $ code-ba-merge n₁ co n₂ p₁ (ap₀ f r) ⟩
        co b⟦ n₁ ⟧a p₁ a⟦ n₂ ⟧b refl₀ b⟦ n₂ ⟧a ap₀ f r a⟦ n₃ ⟧b p₂
          ≡⟨ ap (λ x → x a⟦ n₃ ⟧b p₂) $ ! $ code-ab-swap n₂ (co b⟦ n₁ ⟧a p₁) n₃ r ⟩
        co b⟦ n₁ ⟧a p₁ a⟦ n₂ ⟧b ap₀ g r b⟦ n₃ ⟧a refl₀ a⟦ n₃ ⟧b p₂
          ≡⟨ code-ab-merge n₂ (co b⟦ n₁ ⟧a p₁) n₃ (ap₀ g r) p₂ ⟩∎
        co b⟦ n₁ ⟧a p₁ a⟦ n₂ ⟧b ap₀ g r             ∘₀            p₂
          ∎

    abstract
      code-ab-shift : ∀ {a₂} n₁ co n₂ p₁ n₃ (r : loc n₂ ≡₀ loc n₃) (p₂ : _ ≡₀ a₂)
        → co a⟦ n₁ ⟧b p₁ ∘₀ ap₀ g r b⟦ n₃ ⟧a            p₂
        ≡ co a⟦ n₁ ⟧b p₁            b⟦ n₂ ⟧a ap₀ f r ∘₀ p₂
      code-ab-shift n₁ co n₂ p₁ n₃ r p₂ =
        co a⟦ n₁ ⟧b p₁             ∘₀            ap₀ g r b⟦ n₃ ⟧a p₂
          ≡⟨ ap (λ x → x b⟦ n₃ ⟧a p₂) $ ! $ code-ab-merge n₁ co n₂ p₁ (ap₀ g r) ⟩
        co a⟦ n₁ ⟧b p₁ b⟦ n₂ ⟧a refl₀ a⟦ n₂ ⟧b ap₀ g r b⟦ n₃ ⟧a p₂
          ≡⟨ ap (λ x → x b⟦ n₃ ⟧a p₂) $ ! $ code-ba-swap n₂ (co a⟦ n₁ ⟧b p₁) n₃ r ⟩
        co a⟦ n₁ ⟧b p₁ b⟦ n₂ ⟧a ap₀ f r a⟦ n₃ ⟧b refl₀ b⟦ n₃ ⟧a p₂
          ≡⟨ code-ba-merge n₂ (co a⟦ n₁ ⟧b p₁) n₃ (ap₀ f r) p₂ ⟩∎
        co a⟦ n₁ ⟧b p₁ b⟦ n₂ ⟧a ap₀ f r             ∘₀            p₂
          ∎

  -- Definition of code
  module _ where
    P : Set i
    P = pushout d

    -- Basic conversion
    a⇒b : ∀ n → code-a (f $ loc n) → code-b (g $ loc n)
    a⇒b n co = co a⟦ n ⟧b refl₀

    b⇒a : ∀ n → code-b (g $ loc n) → code-a (f $ loc n)
    b⇒a n co = co b⟦ n ⟧a refl₀

    private
      -- The head of the code
      code-glue-eq-loc : ∀ n → code-a (f $ loc n) ≃ code-b (g $ loc n)
      code-glue-eq-loc n = a⇒b n ,
        iso-is-eq (a⇒b n) (b⇒a n) (code-b-refl-refl n) (code-a-refl-refl n)

    abstract
      trans-code-a-r : ∀ n₁ n₂ (r : loc n₁ ≡ loc n₂) (co : code-a $ f $ loc n₁)
        → transport (code-a ◯ f) r co ≡ co a⟦ n₁ ⟧b refl₀ b⟦ n₁ ⟧a proj (ap f r)
      trans-code-a-r n₁ n₂ r co =
        transport (code-a ◯ f) r co
          ≡⟨ ! $ trans-ap code-a f r co ⟩
        transport code-a (ap f r) co
          ≡⟨ ap (transport code-a $ ap f r) $ ! $ code-a-refl-refl n₁ co ⟩
        transport code-a (ap f r) (co a⟦ n₁ ⟧b refl₀ b⟦ n₁ ⟧a refl₀)
          ≡⟨ trans-ba (ap f r) n₁ _ refl₀ ⟩∎
        co a⟦ n₁ ⟧b refl₀ b⟦ n₁ ⟧a proj (ap f r)
          ∎

    abstract
      trans-code-b-r : ∀ n₁ n₂ (r : loc n₁ ≡ loc n₂) (co : code-b $ g $ loc n₁)
        → transport (code-b ◯ g) r co ≡ co b⟦ n₁ ⟧a refl₀ a⟦ n₁ ⟧b proj (ap g r)
      trans-code-b-r n₁ n₂ r co =
        transport (code-b ◯ g) r co
          ≡⟨ ! $ trans-ap code-b g r co ⟩
        transport code-b (ap g r) co
          ≡⟨ ap (transport code-b $ ap g r) $ ! $ code-b-refl-refl n₁ co ⟩
        transport code-b (ap g r) (co b⟦ n₁ ⟧a refl₀ a⟦ n₁ ⟧b refl₀)
          ≡⟨ trans-ab (ap g r) n₁ _ refl₀ ⟩∎
        co b⟦ n₁ ⟧a refl₀ a⟦ n₁ ⟧b proj (ap g r)
          ∎

    private
      abstract
        code-glue-eq-route : ∀ n₁ n₂ r
          → transport (λ c → code-a (f c) ≃ code-b (g c)) r (code-glue-eq-loc n₁)
          ≡ code-glue-eq-loc n₂
        code-glue-eq-route n₁ n₂ r = equiv-eq $ funext λ co →
          π₁ (transport (λ c → code-a (f c) ≃ code-b (g c)) r (code-glue-eq-loc n₁)) co
              ≡⟨ ap (λ x → x co) $ app-trans
                (λ c →  code-a (f c) ≃ code-b (g c))
                (λ c → code-a (f c) → code-b (g c))
                (λ _ → π₁) r (code-glue-eq-loc n₁) ⟩
          transport (λ c → code-a (f c) → code-b (g c)) r (a⇒b n₁) co
              ≡⟨ trans-→ (code-a ◯ f) (code-b ◯ g) r (a⇒b n₁) co ⟩
          transport (code-b ◯ g) r (a⇒b n₁ $ transport (code-a ◯ f) (! r) co)
              ≡⟨ ap (transport (code-b ◯ g) r ◯ a⇒b n₁) $ trans-code-a-r _ _ (! r) co ⟩
          transport (code-b ◯ g) r (co a⟦ n₂ ⟧b refl₀ b⟦ n₂ ⟧a proj (ap f $ ! r) a⟦ n₁ ⟧b refl₀)
              ≡⟨ ap (λ x → transport (code-b ◯ g) r $ x a⟦ n₁ ⟧b refl₀) $ ! $ code-ab-swap _ co _ (proj $ ! r) ⟩
          transport (code-b ◯ g) r (co a⟦ n₂ ⟧b proj (ap g $ ! r) b⟦ n₁ ⟧a refl₀ a⟦ n₁ ⟧b refl₀)
              ≡⟨ ap (transport (code-b ◯ g) r) $ code-b-refl-refl n₁ _ ⟩
          transport (code-b ◯ g) r (co a⟦ n₂ ⟧b proj (ap g $ ! r))
              ≡⟨ trans-code-b-r _ _ r _ ⟩
          co a⟦ n₂ ⟧b proj (ap g $ ! r) b⟦ n₁ ⟧a refl₀ a⟦ n₁ ⟧b proj (ap g r)
              ≡⟨ code-ab-merge n₂ co n₁ _ _ ⟩
          co a⟦ n₂ ⟧b proj (ap g (! r) ∘ ap g r)
              ≡⟨ ap (λ x → co a⟦ n₂ ⟧b proj x) $ concat-ap g (! r) r ⟩
          co a⟦ n₂ ⟧b proj (ap g $ ! r ∘ r)
              ≡⟨ ap (λ x → co a⟦ n₂ ⟧b proj (ap g x)) $ opposite-left-inverse r ⟩∎
          a⇒b n₂ co
              ∎

    private
      code-glue-eq : ∀ c → code-a (f c) ≃ code-b (g c)
      code-glue-eq = visit-fiber-rec l
        (λ c → code-a (f c) ≃ code-b (g c))
        ⦃ λ _ → ≃-is-set (code-a-is-set _) (code-b-is-set _) ⦄
        code-glue-eq-loc
        code-glue-eq-route

    -- The data type!
    code : P → Set i
    code = pushout-rec-nondep (Set i) code-a code-b (eq-to-path ◯ code-glue-eq)

    -- Useful lemma
    abstract
      trans-code-glue-loc : ∀ n₂ co → transport code (glue $ loc n₂) co ≡ a⇒b n₂ co
      trans-code-glue-loc n₂ co =
        transport code (glue $ loc n₂) co
          ≡⟨ ! $ trans-ap (λ X → X) code (glue $ loc n₂) co ⟩
        transport (λ X → X) (ap code $ glue $ loc n₂) co
          ≡⟨ ap (λ x → transport (λ X → X) x co)
              $ pushout-β-glue-nondep (Set i) code-a code-b (eq-to-path ◯ code-glue-eq) (loc n₂) ⟩
        transport (λ X → X) (eq-to-path $ code-glue-eq $ loc n₂) co
          ≡⟨ ap (λ x → transport (λ X → X) (eq-to-path x) co)
                $ visit-fiber-β-loc l
                    (λ c → code-a (f c) ≃ code-b (g c))
                    ⦃ λ _ → ≃-is-set (code-a-is-set _) (code-b-is-set _) ⦄
                    code-glue-eq-loc
                    code-glue-eq-route
                    n₂ ⟩
        transport (λ X → X) (eq-to-path $ code-glue-eq-loc n₂) co
          ≡⟨ trans-id-eq-to-path (code-glue-eq-loc n₂) co ⟩∎
        a⇒b n₂ co
          ∎

    abstract
      trans-code-!glue-loc : ∀ n₂ co → transport code (! $ glue $ loc n₂) co ≡ b⇒a n₂ co
      trans-code-!glue-loc n₂ co = move!-transp-right code (glue $ loc n₂) co (b⇒a n₂ co) $ ! $
        transport code (glue $ loc n₂) (b⇒a n₂ co)
          ≡⟨ trans-code-glue-loc n₂ (b⇒a n₂ co) ⟩
        a⇒b n₂ (b⇒a n₂ co)
          ≡⟨ code-b-refl-refl n₂ co ⟩∎
        co
          ∎

    -- Truncation level
    abstract
      code-is-set : ∀ p → is-set $ code p
      code-is-set = pushout-rec
        (λ p → is-set $ code p)
        code-a-is-set
        code-b-is-set
        (λ _ → prop-has-all-paths is-set-is-prop _ _)
