{-# OPTIONS --without-K #-}

open import Base

{-
  The truncated representation for paths from a fixed point
  (a₁ here) in one corner of a pushout (A here), split by
  the end points.

       g
    C---->B
    |     |
   f|  ~  |right
    v     v
    A---->P
     left

  The untruncated version is Precode. See OneSidedSplitPrecode.agda.

  This is for formalizing the van Kampen theorem.
-}

module Homotopy.VanKampen.SplitCode {i}
  (C A B : Set i) (f : C → A) (g : C → B) (a₁ : A) where
  
  open import Homotopy.Truncation
  open import Spaces.Pi0PathSpace

  import Homotopy.VanKampen.SplitPrecode C A B f g a₁ as P

  code-a : A → Set i
  code-a = π₀ ◯ P.precode-a

  code-b : B → Set i
  code-b = π₀ ◯ P.precode-b

  abstract
    code-a-is-set : (a : A) → is-set (code-a a)
    code-a-is-set = π₀-is-set ◯ P.precode-a

    code-b-is-set : (b : B) → is-set (code-b b)
    code-b-is-set = π₀-is-set ◯ P.precode-b
  
  abstract
    any-cell₂-a : ∀ {a} {x y : code-a a} (p q : x ≡ y) → p ≡ q
    any-cell₂-a = prop-has-all-paths $ code-a-is-set _ _ _

    any-cell₂-b : ∀ {b} {x y : code-b b} (p q : x ≡ y) → p ≡ q
    any-cell₂-b = prop-has-all-paths $ code-b-is-set _ _ _

  a : ∀ {a₂} → a₁ ≡₀ a₂ → code-a a₂
  a = proj ◯ P.a

  infixl 6 a
  syntax a co = ⟧a co

  ba : ∀ {a₂} c → code-b (g c) → f c ≡₀ a₂ → code-a a₂
  ba c pco p = π₀-extend-nondep
    ⦃ code-a-is-set _ ⦄
    (λ x → proj $ P.ba c x p) pco

  infixl 6 ba
  syntax ba c co p = co b⟦ c ⟧a p

  ab : ∀ {b₂} c → code-a (f c) → g c ≡₀ b₂ → code-b b₂
  ab c pco p = π₀-extend-nondep
    ⦃ code-b-is-set _ ⦄
    (λ x → proj $ P.ab c x p) pco

  infixl 6 ab
  syntax ab c co p = co a⟦ c ⟧b p

  code-a-refl₀ : ∀ {a₂} c p₁ (p₂ : _ ≡₀ a₂)
    → ⟧a p₁ a⟦ c ⟧b refl₀ _ b⟦ c ⟧a p₂
    ≡ ⟧a p₁            ∘₀           p₂
  code-a-refl₀ c p₁ p₂ = ap proj $ P.precode-a-refl₀ c p₁ p₂

  code-ba-refl₀ : ∀ {a₂} c₁ co c₂ p₁ (p₂ : _ ≡₀ a₂)
    → co b⟦ c₁ ⟧a p₁ a⟦ c₂ ⟧b refl₀ _ b⟦ c₂ ⟧a p₂
    ≡ co b⟦ c₁ ⟧a p₁             ∘₀            p₂
  code-ba-refl₀ {a₂} c₁ co c₂ p₁ p₂ = π₀-extend
    {P = λ co → co b⟦ c₁ ⟧a p₁ a⟦ c₂ ⟧b refl₀ _ b⟦ c₂ ⟧a p₂
              ≡ co b⟦ c₁ ⟧a p₁             ∘₀            p₂}
    ⦃ λ _ → ≡-is-set $ code-a-is-set _ ⦄
    (λ x → ap proj $ P.precode-ba-refl₀ {a₂} c₁ x c₂ p₁ p₂) co

  code-ab-refl₀ : ∀ {b₂} c₁ co c₂ p₁ (p₂ : _ ≡₀ b₂)
    → co a⟦ c₁ ⟧b p₁ b⟦ c₂ ⟧a refl₀ _ a⟦ c₂ ⟧b p₂
    ≡ co a⟦ c₁ ⟧b p₁             ∘₀            p₂
  code-ab-refl₀ {b₂} c₁ co c₂ p₁ p₂ = π₀-extend
    {P = λ co → co a⟦ c₁ ⟧b p₁ b⟦ c₂ ⟧a refl₀ _ a⟦ c₂ ⟧b p₂
              ≡ co a⟦ c₁ ⟧b p₁             ∘₀            p₂}
    ⦃ λ _ → ≡-is-set $ code-b-is-set _ ⦄
    (λ x → ap proj $ P.precode-ab-refl₀ {b₂} c₁ x c₂ p₁ p₂) co

  code-rec : ∀ {j}
    (P-a : ∀ {a₂} → code-a a₂ → Set j) ⦃ _ : ∀ {a₂} co → is-set $ P-a {a₂} co ⦄
    (P-b : ∀ {b₂} → code-b b₂ → Set j) ⦃ _ : ∀ {b₂} co → is-set $ P-b {b₂} co ⦄
    (h₀-a : ∀ {a₂} (p : _ ≡₀ a₂) → P-a (a p))
    (h₀-ba : ∀ {a₂} c {co} (_ : P-b co) (p : _ ≡₀ a₂)
      → P-a (co b⟦ c ⟧a p))
    (h₀-ab : ∀ {b₂} c {co} (_ : P-a co) (p : _ ≡₀ b₂)
      → P-b (co a⟦ c ⟧b p))
    (h₁-a : ∀ {a₂} c p₁ (p₂ : _ ≡₀ a₂) →
      transport P-a (code-a-refl₀ c p₁ p₂)
        (h₀-ba c (h₀-ab c (h₀-a p₁) (refl₀ _)) p₂)
      ≡ h₀-a (p₁ ∘₀ p₂))
    (h₁-ba : ∀ {a₂} c₁ {co} (pco : P-b co) c₂ p₁ (p₂ : _ ≡₀ a₂) →
      transport P-a (code-ba-refl₀ c₁ co c₂ p₁ p₂)
        (h₀-ba c₂ (h₀-ab c₂ (h₀-ba c₁ pco p₁) (refl₀ _)) p₂)
      ≡ (h₀-ba c₁ pco (p₁ ∘₀ p₂)))
    (h₁-ab : ∀ {b₂} c₁ {co} (pco : P-a co) c₂ p₁ (p₂ : _ ≡₀ b₂) →
      transport P-b (code-ab-refl₀ c₁ co c₂ p₁ p₂)
        (h₀-ab c₂ (h₀-ba c₂ (h₀-ab c₁ pco p₁) (refl₀ _)) p₂)
      ≡ (h₀-ab c₁ pco (p₁ ∘₀ p₂)))
    → (∀ {a₂} (co : code-a a₂) → P-a co)
    × (∀ {b₂} (co : code-b b₂) → P-b co)
  code-rec P-a ⦃ P-a-is-set ⦄ P-b ⦃ P-b-is-set ⦄ h₀-a h₀-ba h₀-ab h₁-a h₁-ba h₁-ab = elim-a , elim-b
    where
      h₀′-a = h₀-a

      h₀′-ba : ∀ {a₂} c {co} (_ : P-b $ proj co) (p : _ ≡₀ a₂) → P-a (proj co b⟦ c ⟧a p)
      h₀′-ba c {co} = h₀-ba c {proj co}
      
      h₀′-ab : ∀ {b₂} c {co} (_ : P-a $ proj co) (p : _ ≡₀ b₂) → P-b (proj co a⟦ c ⟧b p)
      h₀′-ab c {co} = h₀-ab c {proj co}

      abstract
        h₁′-a : ∀ {a₂} c p₁ (p₂ : _ ≡₀ a₂) →
          transport (P-a ◯ proj) (P.precode-a-refl₀ c p₁ p₂)
            (h₀-ba c (h₀-ab c (h₀-a p₁) (refl₀ _)) p₂)
          ≡ h₀-a (p₁ ∘₀ p₂)
        h₁′-a c p₁ p₂ =
          transport (P-a ◯ proj) (P.precode-a-refl₀ c p₁ p₂)
            (h₀-ba c (h₀-ab c (h₀-a p₁) (refl₀ _)) p₂)
              ≡⟨ ! $ trans-ap {P = P-a} proj (P.precode-a-refl₀ c p₁ p₂) _ ⟩
          transport P-a (code-a-refl₀ c p₁ p₂)
            (h₀-ba c (h₀-ab c (h₀-a p₁) (refl₀ _)) p₂)
              ≡⟨ h₁-a c p₁ p₂ ⟩∎
          h₀-a (p₁ ∘₀ p₂)
              ∎

      abstract
        h₁′-ba : ∀ {a₂} c₁ {co} (pco : P-b $ proj co) c₂ p₁ (p₂ : _ ≡₀ a₂) →
          transport (P-a ◯ proj) (P.precode-ba-refl₀ c₁ co c₂ p₁ p₂)
            (h₀-ba c₂ (h₀-ab c₂ (h₀-ba c₁ pco p₁) (refl₀ _)) p₂)
          ≡ (h₀-ba c₁ pco (p₁ ∘₀ p₂))
        h₁′-ba c₁ {co} pco c₂ p₁ p₂ =
          transport (P-a ◯ proj) (P.precode-ba-refl₀ c₁ co c₂ p₁ p₂)
            (h₀-ba c₂ (h₀-ab c₂ (h₀-ba c₁ pco p₁) (refl₀ _)) p₂)
              ≡⟨ ! $ trans-ap {P = P-a} proj (P.precode-ba-refl₀ c₁ co c₂ p₁ p₂) _ ⟩
          transport P-a (code-ba-refl₀ c₁ (proj co) c₂ p₁ p₂)
            (h₀-ba c₂ (h₀-ab c₂ (h₀-ba c₁ pco p₁) (refl₀ _)) p₂)
              ≡⟨ h₁-ba c₁ pco c₂ p₁ p₂ ⟩∎
          h₀-ba c₁ pco (p₁ ∘₀ p₂)
              ∎

      abstract
        h₁′-ab : ∀ {b₂} c₁ {co} (pco : P-a $ proj co) c₂ p₁ (p₂ : _ ≡₀ b₂) →
          transport (P-b ◯ proj) (P.precode-ab-refl₀ c₁ co c₂ p₁ p₂)
            (h₀-ab c₂ (h₀-ba c₂ (h₀-ab c₁ pco p₁) (refl₀ _)) p₂)
          ≡ (h₀-ab c₁ pco (p₁ ∘₀ p₂))
        h₁′-ab c₁ {co} pco c₂ p₁ p₂ =
          transport (P-b ◯ proj) (P.precode-ab-refl₀ c₁ co c₂ p₁ p₂)
            (h₀-ab c₂ (h₀-ba c₂ (h₀-ab c₁ pco p₁) (refl₀ _)) p₂)
              ≡⟨ ! $ trans-ap {P = P-b} proj (P.precode-ab-refl₀ c₁ co c₂ p₁ p₂) _ ⟩
          transport P-b (code-ab-refl₀ c₁ (proj co) c₂ p₁ p₂)
            (h₀-ab c₂ (h₀-ba c₂ (h₀-ab c₁ pco p₁) (refl₀ _)) p₂)
              ≡⟨ h₁-ab c₁ pco c₂ p₁ p₂ ⟩∎
          h₀-ab c₁ pco (p₁ ∘₀ p₂)
              ∎

      elim′ : (∀ {a₂} (co : P.precode-a a₂) → P-a $ proj co)
            × (∀ {b₂} (co : P.precode-b b₂) → P-b $ proj co)
      elim′ = P.precode-rec (P-a ◯ proj) (P-b ◯ proj) h₀′-a h₀′-ba h₀′-ab h₁′-a h₁′-ba h₁′-ab

      elim-a : (∀ {a₂} (co : code-a a₂) → P-a co)
      elim-a {a₂} co = π₀-extend ⦃ P-a-is-set {a₂} ⦄ (λ x → π₁ elim′ x) co

      elim-b : (∀ {b₂} (co : code-b b₂) → P-b co)
      elim-b {b₂} co = π₀-extend ⦃ P-b-is-set {b₂} ⦄ (λ x → π₂ elim′ x) co

  code-rec-nondep : ∀ {j}
    (P-a : A → Set j) ⦃ _ : ∀ a → is-set $ P-a a ⦄
    (P-b : B → Set j) ⦃ _ : ∀ b → is-set $ P-b b ⦄
    (h₀-a : ∀ {a₂} (p : a₁ ≡₀ a₂) → P-a a₂)
    (h₀-ba : ∀ {a₂} c {co : code-b (g c)} → P-b (g c) → f c ≡₀ a₂ → P-a a₂)
    (h₀-ab : ∀ {b₂} c {co : code-a (f c)} → P-a (f c) → g c ≡₀ b₂ → P-b b₂)
    (h₁-a : ∀ {a₂} c (p₁ : a₁ ≡₀ f c) (p₂ : f c ≡₀ a₂) →
        (h₀-ba c {ab c (a p₁) (refl₀ _)}
          (h₀-ab c {a p₁} (h₀-a p₁) (refl₀ _)) p₂)
      ≡ h₀-a (p₁ ∘₀ p₂))
    (h₁-ba : ∀ {a₂} c₁ {co} (pco : P-b (g c₁)) c₂ p₁ (p₂ : _ ≡₀ a₂) →
        (h₀-ba c₂ {ab c₂ (ba c₁ co p₁) (refl₀ _)}
          (h₀-ab c₂ {ba c₁ co p₁}
            (h₀-ba c₁ {co} pco p₁)
            (refl₀ _))
          p₂)
      ≡ (h₀-ba c₁ {co} pco (p₁ ∘₀ p₂)))
    (h₁-ab : ∀ {b₂} c₁ {co} (pco : P-a (f c₁)) c₂ p₁ (p₂ : _ ≡₀ b₂) →
        (h₀-ab c₂ {ba c₂ (ab c₁ co p₁) (refl₀ _)}
          (h₀-ba c₂ {ab c₁ co p₁}
            (h₀-ab c₁ {co} pco p₁)
            (refl₀ _))
          p₂)
      ≡ (h₀-ab c₁ {co} pco (p₁ ∘₀ p₂)))
    → (∀ {a₂} (co : code-a a₂) → P-a a₂)
    × (∀ {b₂} (co : code-b b₂) → P-b b₂)
  code-rec-nondep P-a ⦃ P-a-is-set ⦄ P-b ⦃ P-b-is-set ⦄ h₀-a h₀-ba h₀-ab h₁-a h₁-ba h₁-ab = elim-a , elim-b
    where
      h₀′-a = h₀-a

      h₀′-ba : ∀ {a₂} c {co : P.precode-b (g c)} → P-b (g c) → f c ≡₀ a₂ → P-a a₂
      h₀′-ba c {co} = h₀-ba c {proj co}
      
      h₀′-ab : ∀ {b₂} c {co : P.precode-a (f c)} → P-a (f c) → g c ≡₀ b₂ → P-b b₂
      h₀′-ab c {co} = h₀-ab c {proj co}

      abstract
        h₁′-a : ∀ {a₂} c (p₁ : a₁ ≡₀ f c) (p₂ : f c ≡₀ a₂) →
            (h₀-ba c {ab c (a p₁) (refl₀ _)}
              (h₀-ab c {a p₁} (h₀-a p₁) (refl₀ _)) p₂)
          ≡ h₀-a (p₁ ∘₀ p₂)
        h₁′-a c p₁ p₂ = h₁-a c p₁ p₂

      abstract
        h₁′-ba : ∀ {a₂} c₁ {co} (pco : P-b (g c₁)) c₂ p₁ (p₂ : _ ≡₀ a₂) →
            (h₀′-ba c₂ {P.ab c₂ (P.ba c₁ co p₁) (refl₀ _)}
              (h₀′-ab c₂ {P.ba c₁ co p₁}
                (h₀′-ba c₁ {co} pco p₁)
                (refl₀ _))
              p₂)
          ≡ (h₀′-ba c₁ {co} pco (p₁ ∘₀ p₂))
        h₁′-ba c₁ {co} pco c₂ p₁ p₂ = h₁-ba c₁ {proj co} pco c₂ p₁ p₂

      abstract
        h₁′-ab : ∀ {b₂} c₁ {co} (pco : P-a (f c₁)) c₂ p₁ (p₂ : _ ≡₀ b₂) →
            (h₀′-ab c₂ {P.ba c₂ (P.ab c₁ co p₁) (refl₀ _)}
              (h₀′-ba c₂ {P.ab c₁ co p₁}
                (h₀′-ab c₁ {co} pco p₁)
                (refl₀ _))
              p₂)
          ≡ (h₀′-ab c₁ {co} pco (p₁ ∘₀ p₂))
        h₁′-ab c₁ {co} pco c₂ p₁ p₂ = h₁-ab c₁ {proj co} pco c₂ p₁ p₂

      elim′ : (∀ {a₂} (co : P.precode-a a₂) → P-a a₂)
            × (∀ {b₂} (co : P.precode-b b₂) → P-b b₂)
      elim′ = P.precode-rec-nondep P-a P-b h₀′-a h₀′-ba h₀′-ab h₁′-a h₁′-ba h₁′-ab

      elim-a : (∀ {a₂} (co : code-a a₂) → P-a a₂)
      elim-a {a₂} co = π₀-extend-nondep ⦃ P-a-is-set a₂ ⦄ (λ x → π₁ elim′ {a₂} x) co

      elim-b : (∀ {b₂} (co : code-b b₂) → P-b b₂)
      elim-b {b₂} co = π₀-extend-nondep ⦃ P-b-is-set b₂ ⦄ (λ x → π₂ elim′ {b₂} x) co

  code-rec-a : ∀ {j}
    (P-a : ∀ {a₂} → code-a a₂ → Set j) ⦃ _ : ∀ {a₂} co → is-set $ P-a {a₂} co ⦄
    (h₀-a : ∀ {a₂} (p : _ ≡₀ a₂) → P-a (a p))
    (h₀-ba : ∀ {a₂} c co (p : _ ≡₀ a₂) → P-a (co b⟦ c ⟧a p))
    (h₁-a : ∀ {a₂} c p₁ (p₂ : _ ≡₀ a₂) →
      transport P-a (code-a-refl₀ c p₁ p₂)
        (h₀-ba c (⟧a p₁ a⟦ c ⟧b refl₀ _) p₂)
      ≡ h₀-a (p₁ ∘₀ p₂))
    (h₁-ba : ∀ {a₂} c₁ co c₂ p₁ (p₂ : _ ≡₀ a₂) →
      transport P-a (code-ba-refl₀ c₁ co c₂ p₁ p₂)
        (h₀-ba c₂ (co b⟦ c₁ ⟧a p₁ a⟦ c₂ ⟧b refl₀ _) p₂)
      ≡ (h₀-ba c₁ co (p₁ ∘₀ p₂)))
    → (∀ {a₂} (co : code-a a₂) → P-a co)
  code-rec-a {j} P-a ⦃ P-a-is-set ⦄ h₀-a h₀-ba h₁-a h₁-ba = elim-a
    where
      P-b : ∀ {b₂} → code-b b₂ → Set j
      P-b = λ _ → unit

      P-b-is-set : ∀ {b₂} co → is-set (P-b {b₂} co)
      P-b-is-set = λ _ → unit-is-set

      h₀′-a : ∀ {a₂} (p : _ ≡₀ a₂) → P-a (a p)
      h₀′-a = h₀-a

      h₀′-ba : ∀ {a₂} c {co} (_ : P-b co) (p : f c ≡₀ a₂) → P-a (co b⟦ c ⟧a p)
      h₀′-ba c {co} _ = h₀-ba c co
      
      h₀′-ab : ∀ {b₂} c {co} (_ : P-a co) (p : _ ≡₀ b₂) → P-b (co a⟦ c ⟧b p)
      h₀′-ab _ _ _ = tt

      abstract
        h₁′-a : ∀ {a₂} c (p₁ : a₁ ≡₀ f c) (p₂ : f c ≡₀ a₂) →
          transport P-a (code-a-refl₀ c p₁ p₂)
            (h₀-ba c (ab c (a p₁) (refl₀ _)) p₂)
          ≡ h₀-a (p₁ ∘₀ p₂)
        h₁′-a = h₁-a

      abstract
        h₁′-ba : ∀ {a₂} c₁ {co} (pco : P-b co) c₂ p₁ (p₂ : _ ≡₀ a₂) →
          transport P-a (code-ba-refl₀ c₁ co c₂ p₁ p₂)
            (h₀-ba c₂ (co b⟦ c₁ ⟧a p₁ a⟦ c₂ ⟧b refl₀ _) p₂)
          ≡ (h₀-ba c₁ co (p₁ ∘₀ p₂))
        h₁′-ba c₁ {co} _ = h₁-ba c₁ co

      abstract
        h₁′-ab : ∀ {b₂} c₁ {co} (pco : P-a co) c₂ p₁ (p₂ : _ ≡₀ b₂) →
          transport P-b (code-ab-refl₀ c₁ co c₂ p₁ p₂) tt ≡ tt
        h₁′-ab _ _ _ _ _ = prop-has-all-paths unit-is-prop _ _

      elim-a : ∀ {a₂} (co : code-a a₂) → P-a co
      elim-a = π₁ $ code-rec P-a ⦃ P-a-is-set ⦄ P-b ⦃ P-b-is-set ⦄
                      h₀′-a h₀′-ba h₀′-ab h₁′-a h₁′-ba h₁′-ab

  code-rec-b : ∀ {j}
    (P-b : ∀ {b₂} → code-b b₂ → Set j) ⦃ _ : ∀ {b₂} co → is-set $ P-b {b₂} co ⦄
    (h₀-ab : ∀ {b₂} c co (p : _ ≡₀ b₂) → P-b (co a⟦ c ⟧b p))
    (h₁-ab : ∀ {b₂} c₁ co c₂ p₁ (p₂ : _ ≡₀ b₂) →
      transport P-b (code-ab-refl₀ c₁ co c₂ p₁ p₂)
        (h₀-ab c₂ (co a⟦ c₁ ⟧b p₁ b⟦ c₂ ⟧a refl₀ _) p₂)
      ≡ (h₀-ab c₁ co (p₁ ∘₀ p₂)))
    → (∀ {b₂} (co : code-b b₂) → P-b co)
  code-rec-b {j} P-b ⦃ P-b-is-set ⦄ h₀-ab h₁-ab = elim-b
    where
      P-a : ∀ {a₂} → code-a a₂ → Set j
      P-a = λ _ → unit

      P-a-is-set : ∀ {a₂} co → is-set (P-a {a₂} co)
      P-a-is-set = λ _ → unit-is-set

      h₀′-a : ∀ {a₂} (p : _ ≡₀ a₂) → P-a (a p)
      h₀′-a _ = tt

      h₀′-ba : ∀ {a₂} c {co} (_ : P-b co) (p : f c ≡₀ a₂) → P-a (co b⟦ c ⟧a p)
      h₀′-ba _ _ _ = tt
      
      h₀′-ab : ∀ {b₂} c {co} (_ : P-a co) (p : _ ≡₀ b₂) → P-b (co a⟦ c ⟧b p)
      h₀′-ab c {co} _ = h₀-ab c co

      abstract
        h₁′-a : ∀ {a₂} c (p₁ : a₁ ≡₀ f c) (p₂ : f c ≡₀ a₂) →
          transport P-a (code-a-refl₀ c p₁ p₂) tt ≡ tt
        h₁′-a _ _ _ = prop-has-all-paths unit-is-prop _ _

      abstract
        h₁′-ba : ∀ {a₂} c₁ {co} (pco : P-b co) c₂ p₁ (p₂ : _ ≡₀ a₂) →
          transport P-a (code-ba-refl₀ c₁ co c₂ p₁ p₂) tt ≡ tt
        h₁′-ba _ _ _ _ _ = prop-has-all-paths unit-is-prop _ _

      abstract
        h₁′-ab : ∀ {b₂} c₁ {co} (pco : P-a co) c₂ p₁ (p₂ : _ ≡₀ b₂) →
          transport P-b (code-ab-refl₀ c₁ co c₂ p₁ p₂)
            (h₀-ab c₂ (co a⟦ c₁ ⟧b p₁ b⟦ c₂ ⟧a refl₀ _) p₂)
          ≡ (h₀-ab c₁ co (p₁ ∘₀ p₂))
        h₁′-ab c₁ {co} _ = h₁-ab c₁ co

      elim-b : ∀ {b₂} (co : code-b b₂) → P-b co
      elim-b = π₂ $ code-rec P-a ⦃ P-a-is-set ⦄ P-b ⦃ P-b-is-set ⦄
                      h₀′-a h₀′-ba h₀′-ab h₁′-a h₁′-ba h₁′-ab

