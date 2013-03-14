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

  module _ where
    private
      data #code-a (a₂ : A) : Set i
      data #code-b (b₂ : B) : Set i

      data #code-a a₂ where
        #a : a₁ ≡₀ a₂ → #code-a a₂
        #ba : ∀ c → #code-b (g c) → f c ≡₀ a₂ → #code-a a₂
      data #code-b b₂ where
        #ab : ∀ c → #code-a (f c) → g c ≡₀ b₂ → #code-b b₂

    code-b : B → Set i
    code-b = #code-b

    code-a : A → Set i
    code-a = #code-a

    postulate -- HIT
      code-a-is-set : {a : A} → is-set (code-a a)
      code-b-is-set : {b : B} → is-set (code-b b)

    a : ∀ {a₂} → a₁ ≡₀ a₂ → code-a a₂
    a = #a

    infixl 6 a
    syntax a co = ⟧a co

    ba : ∀ {a₂} c → code-b (g c) → f c ≡₀ a₂ → code-a a₂
    ba = #ba

    infixl 6 ba
    syntax ba c co p = co b⟦ c ⟧a p

    ab : ∀ {b₂} c → code-a (f c) → g c ≡₀ b₂ → code-b b₂
    ab = #ab

    infixl 6 ab
    syntax ab c co p = co a⟦ c ⟧b p

    {-
      Intuition: If you cross the bridge (c : C) and
      return immediately (refl₀ and then the same c),
      then this is equivalent to not crossing the bridge.

      co                       co
      \------------\           |
          <c>      | refl   ≡  |
      /------------/           |
      p₂                       p₂

      The following three rules are for three different
      constructs. There seems to be a way to write only
      two rules, but that seems to require a hacky function
      ignoring 1-cells. I don′t want to have such functions.
    -}
    postulate -- HIT
      code-a-refl₀ : ∀ {a₂} c p₁ (p₂ : _ ≡₀ a₂)
        → ⟧a p₁ a⟦ c ⟧b refl₀ _ b⟦ c ⟧a p₂
        ≡ ⟧a p₁            ∘₀           p₂
      code-ba-refl₀ : ∀ {a₂} c₁ co c₂ p₁ (p₂ : _ ≡₀ a₂)
        → co b⟦ c₁ ⟧a p₁ a⟦ c₂ ⟧b refl₀ _ b⟦ c₂ ⟧a p₂
        ≡ co b⟦ c₁ ⟧a p₁             ∘₀            p₂
      code-ab-refl₀ : ∀ {b₂} c₁ co c₂ p₁ (p₂ : _ ≡₀ b₂)
        → co a⟦ c₁ ⟧b p₁ b⟦ c₂ ⟧a refl₀ _ a⟦ c₂ ⟧b p₂
        ≡ co a⟦ c₁ ⟧b p₁             ∘₀            p₂

    -- dependent recursor
    code-rec : ∀ {j}
      (P-a : ∀ {a₂} → code-a a₂ → Set j) ⦃ _ : ∀ {a₂} co → is-set $ P-a {a₂} co ⦄
      (P-b : ∀ {b₂} → code-b b₂ → Set j) ⦃ _ : ∀ {b₂} co → is-set $ P-b {b₂} co ⦄
      (h₀-a : ∀ {a₂} (p : _ ≡₀ a₂) → P-a (a p))
      (h₀-ba : ∀ {a₂} c {co} (_ : P-b co) (p : _ ≡₀ a₂)
        → P-a (co b⟦ c ⟧a p))
      (h₀-ab : ∀ {b₂} c {co} (_ : P-a co) (p : _ ≡₀ b₂)
        → P-b (co a⟦ c ⟧b p))
      (h₁-a : ∀ {a₂} c p₁ (p₂ : _ ≡₀ a₂) →
        transport (P-a {a₂}) (code-a-refl₀ c p₁ p₂)
          (h₀-ba c (h₀-ab c (h₀-a p₁) (refl₀ _)) p₂)
        ≡ h₀-a (p₁ ∘₀ p₂))
      (h₁-ba : ∀ {a₂} c₁ {co} (pco : P-b co) c₂ p₁ (p₂ : _ ≡₀ a₂) →
        transport (P-a {a₂}) (code-ba-refl₀ c₁ co c₂ p₁ p₂)
          (h₀-ba c₂ (h₀-ab c₂ (h₀-ba c₁ pco p₁) (refl₀ _)) p₂)
        ≡ (h₀-ba c₁ pco (p₁ ∘₀ p₂)))
      (h₁-ab : ∀ {b₂} c₁ {co} (pco : P-a co) c₂ p₁ (p₂ : _ ≡₀ b₂) →
        transport (P-b {b₂}) (code-ab-refl₀ c₁ co c₂ p₁ p₂)
          (h₀-ab c₂ (h₀-ba c₂ (h₀-ab c₁ pco p₁) (refl₀ _)) p₂)
        ≡ (h₀-ab c₁ pco (p₁ ∘₀ p₂)))
      → (∀ {a₂} (co : code-a a₂) → P-a co)
      × (∀ {b₂} (co : code-b b₂) → P-b co)
    code-rec P-a P-b h₀-a h₀-ba h₀-ab _ _ _ = elim-a , elim-b
      where
        elim-a : ∀ {a₂} (co : code-a a₂) → P-a co
        elim-b : ∀ {b₂} (co : code-b b₂) → P-b co
        elim-a (#a       p) = h₀-a                p
        elim-a (#ba c co p) = h₀-ba c (elim-b co) p
        elim-b (#ab c co p) = h₀-ab c (elim-a co) p

    -- This is actually "partially dependent".
    -- P-a and P-b are indexed by the end points.
    -- This is fine because they are fixed in
    -- all transports in 1-cells.
    code-rec-nondep : ∀ {j}
      (P-a : A → Set j) ⦃ _ : ∀ a → is-set $ P-a a ⦄
      (P-b : B → Set j) ⦃ _ : ∀ b → is-set $ P-b b ⦄
      (h₀-a : ∀ {a₂} (p : a₁ ≡₀ a₂) → P-a a₂)
      (h₀-ba : ∀ {a₂} c {co : code-b (g c)} → P-b (g c) → f c ≡₀ a₂ → P-a a₂)
      (h₀-ab : ∀ {b₂} c {co : code-a (f c)} → P-a (f c) → g c ≡₀ b₂ → P-b b₂)
      (h₁-a : ∀ {a₂} c p₁ (p₂ : _ ≡₀ a₂) →
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
    code-rec-nondep P-a P-b h₀-a h₀-ba h₀-ab _ _ _ = elim-a , elim-b
      where
        elim-a : ∀ {a₂} (co : code-a a₂) → P-a a₂
        elim-b : ∀ {b₂} (co : code-b b₂) → P-b b₂
        elim-a (#a       p) = h₀-a                     p
        elim-a (#ba c co p) = h₀-ba c {co} (elim-b co) p
        elim-b (#ab c co p) = h₀-ab c {co} (elim-a co) p

  module _ where

    abstract
      code-has-all-cells₂-a : ∀ {a} {x y : code-a a} (p q : x ≡ y) → p ≡ q
      code-has-all-cells₂-a = prop-has-all-paths $ code-a-is-set _ _

      code-has-all-cells₂-b : ∀ {b} {x y : code-b b} (p q : x ≡ y) → p ≡ q
      code-has-all-cells₂-b = prop-has-all-paths $ code-b-is-set _ _

    -- Non-recursive recursor
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
    code-rec-a {j} P-a ⦃ P-a-is-set ⦄ h₀-a h₀-ba h₁-a h₁-ba = π₁ $ code-rec
      P-a ⦃ P-a-is-set ⦄
      (λ _ → unit) ⦃ λ _ → unit-is-set ⦄
      h₀-a
      (λ c {co} _ → h₀-ba c co)
      (λ _ _ _ → tt)
      h₁-a
      (λ c₁ {co} _ → h₁-ba c₁ co)
      (λ _ _ _ _ _ → prop-has-all-paths unit-is-prop _ _)

    code-rec-b : ∀ {j}
      (P-b : ∀ {b₂} → code-b b₂ → Set j) ⦃ _ : ∀ {b₂} co → is-set $ P-b {b₂} co ⦄
      (h₀-ab : ∀ {b₂} c co (p : _ ≡₀ b₂) → P-b (co a⟦ c ⟧b p))
      (h₁-ab : ∀ {b₂} c₁ co c₂ p₁ (p₂ : _ ≡₀ b₂) →
        transport P-b (code-ab-refl₀ c₁ co c₂ p₁ p₂)
          (h₀-ab c₂ (co a⟦ c₁ ⟧b p₁ b⟦ c₂ ⟧a refl₀ _) p₂)
        ≡ (h₀-ab c₁ co (p₁ ∘₀ p₂)))
      → (∀ {b₂} (co : code-b b₂) → P-b co)
    code-rec-b {j} P-b ⦃ P-b-is-set ⦄ h₀-ab h₁-ab = π₂ $ code-rec
      (λ _ → unit) ⦃ λ _ → unit-is-set ⦄
      P-b ⦃ P-b-is-set ⦄
      (λ _ → tt)
      (λ _ _ _ → tt)
      (λ c {co} _ → h₀-ab c co)
      (λ _ _ _ → prop-has-all-paths unit-is-prop _ _)
      (λ _ _ _ _ _ → prop-has-all-paths unit-is-prop _ _)
      (λ c₁ {co} _ → h₁-ab c₁ co)
