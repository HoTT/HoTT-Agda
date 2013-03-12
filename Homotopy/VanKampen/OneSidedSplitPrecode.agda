{-# OPTIONS --without-K #-}

open import Base

{-
  The untruncated representation for paths from a fixed point
  (a₁ here) in one corner of a pushout (A here).

       g
    C---->B
    |     |
   f|  ~  |right
    v     v
    A---->P
     left

  The truncated version is Code. See OneSidedCode.agda.

  This is for formalizing the van Kampen thereom.
-}

module Homotopy.VanKampen.OneSidedSplitPrecode {i}
  (C A B : Set i) (f : C → A) (g : C → B)
  (a₁ : A) where

  open import Spaces.Pi0PathSpace

  module _ where
    private
      data #precode-a (a₂ : A) : Set i
      data #precode-b (b₂ : B) : Set i

      data #precode-a a₂ where
        #a : a₁ ≡₀ a₂ → #precode-a a₂
        #ba : ∀ c → #precode-b (g c) → f c ≡₀ a₂ → #precode-a a₂
      data #precode-b b₂ where
        #ab : ∀ c → #precode-a (f c) → g c ≡₀ b₂ → #precode-b b₂

    precode-b : B → Set i
    precode-b = #precode-b

    precode-a : A → Set i
    precode-a = #precode-a

    a : ∀ {a₂} → a₁ ≡₀ a₂ → #precode-a a₂
    a = #a

    infixl 6 a
    syntax a co = ⟧a co

    ba : ∀ {a₂} c → precode-b (g c) → f c ≡₀ a₂ → precode-a a₂
    ba = #ba

    infixl 6 ba
    syntax ba c co p = co b⟦ c ⟧a p

    ab : ∀ {b₂} c → precode-a (f c) → g c ≡₀ b₂ → precode-b b₂
    ab = #ab

    infixl 6 ab
    syntax ab c co p = co a⟦ c ⟧b p

    postulate -- HIT
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
      precode-a-refl₀ : ∀ {a₂} c p₁ (p₂ : _ ≡₀ a₂)
        → ⟧a p₁ a⟦ c ⟧b refl₀ _ b⟦ c ⟧a p₂
        ≡ ⟧a p₁            ∘₀           p₂
      precode-ba-refl₀ : ∀ {a₂} c₁ co c₂ p₁ (p₂ : _ ≡₀ a₂)
        → co b⟦ c₁ ⟧a p₁ a⟦ c₂ ⟧b refl₀ _ b⟦ c₂ ⟧a p₂
        ≡ co b⟦ c₁ ⟧a p₁             ∘₀            p₂
      precode-ab-refl₀ : ∀ {b₂} c₁ co c₂ p₁ (p₂ : _ ≡₀ b₂)
        → co a⟦ c₁ ⟧b p₁ b⟦ c₂ ⟧a refl₀ _ a⟦ c₂ ⟧b p₂
        ≡ co a⟦ c₁ ⟧b p₁             ∘₀            p₂

    precode-rec : ∀ {j}
      (P-a : ∀ {a₂} → precode-a a₂ → Set j)
      (P-b : ∀ {b₂} → precode-b b₂ → Set j)
      (h₀-a : ∀ {a₂} (p : _ ≡₀ a₂) → P-a (a p))
      (h₀-ba : ∀ {a₂} c {co} (_ : P-b co) (p : _ ≡₀ a₂)
        → P-a (co b⟦ c ⟧a p))
      (h₀-ab : ∀ {b₂} c {co} (_ : P-a co) (p : _ ≡₀ b₂)
        → P-b (co a⟦ c ⟧b p))
      (h₁-a : ∀ {a₂} c p₁ (p₂ : _ ≡₀ a₂) →
        transport (P-a {a₂}) (precode-a-refl₀ c p₁ p₂)
          (h₀-ba c (h₀-ab c (h₀-a p₁) (refl₀ _)) p₂)
        ≡ h₀-a (p₁ ∘₀ p₂))
      (h₁-ba : ∀ {a₂} c₁ {co} (pco : P-b co) c₂ p₁ (p₂ : _ ≡₀ a₂) →
        transport (P-a {a₂}) (precode-ba-refl₀ c₁ co c₂ p₁ p₂)
          (h₀-ba c₂ (h₀-ab c₂ (h₀-ba c₁ pco p₁) (refl₀ _)) p₂)
        ≡ (h₀-ba c₁ pco (p₁ ∘₀ p₂)))
      (h₁-ab : ∀ {b₂} c₁ {co} (pco : P-a co) c₂ p₁ (p₂ : _ ≡₀ b₂) →
        transport (P-b {b₂}) (precode-ab-refl₀ c₁ co c₂ p₁ p₂)
          (h₀-ab c₂ (h₀-ba c₂ (h₀-ab c₁ pco p₁) (refl₀ _)) p₂)
        ≡ (h₀-ab c₁ pco (p₁ ∘₀ p₂)))
      → (∀ {a₂} (co : precode-a a₂) → P-a co)
      × (∀ {b₂} (co : precode-b b₂) → P-b co)
    precode-rec P-a P-b h₀-a h₀-ba h₀-ab _ _ _ = elim-a , elim-b
      where
        elim-a : ∀ {a₂} (co : precode-a a₂) → P-a co
        elim-b : ∀ {b₂} (co : precode-b b₂) → P-b co
        elim-a (#a       p) = h₀-a                p
        elim-a (#ba c co p) = h₀-ba c (elim-b co) p
        elim-b (#ab c co p) = h₀-ab c (elim-a co) p

    precode-rec-nondep : ∀ {j} (P-a P-b : Set j)
      (h₀-a : ∀ {a₂} (p : a₁ ≡₀ a₂) → P-a)
      (h₀-ba : ∀ {a₂} c {co : precode-b (g c)} → P-b → f c ≡₀ a₂ → P-a)
      (h₀-ab : ∀ {b₂} c {co : precode-a (f c)} → P-a → g c ≡₀ b₂ → P-b)
      (h₁-a : ∀ {a₂} c p₁ (p₂ : _ ≡₀ a₂) →
          (h₀-ba c {ab c (a p₁) (refl₀ _)}
            (h₀-ab c {a p₁} (h₀-a p₁) (refl₀ _)) p₂)
        ≡ h₀-a (p₁ ∘₀ p₂))
      (h₁-ba : ∀ {a₂} c₁ {co} (pco : P-b) c₂ p₁ (p₂ : _ ≡₀ a₂) →
          (h₀-ba c₂ {ab c₂ (ba c₁ co p₁) (refl₀ _)}
            (h₀-ab c₂ {ba c₁ co p₁}
              (h₀-ba c₁ {co} pco p₁)
              (refl₀ _))
            p₂)
        ≡ (h₀-ba c₁ {co} pco (p₁ ∘₀ p₂)))
      (h₁-ab : ∀ {b₂} c₁ {co} (pco : P-a) c₂ p₁ (p₂ : _ ≡₀ b₂) →
          (h₀-ab c₂ {ba c₂ (ab c₁ co p₁) (refl₀ _)}
            (h₀-ba c₂ {ab c₁ co p₁}
              (h₀-ab c₁ {co} pco p₁)
              (refl₀ _))
            p₂)
        ≡ (h₀-ab c₁ {co} pco (p₁ ∘₀ p₂)))
      → (∀ {a₂} (co : precode-a a₂) → P-a)
      × (∀ {b₂} (co : precode-b b₂) → P-b)
    precode-rec-nondep P-a P-b h₀-a h₀-ba h₀-ab _ _ _ = elim-a , elim-b
      where
        elim-a : ∀ {a₂} (co : precode-a a₂) → P-a
        elim-b : ∀ {b₂} (co : precode-b b₂) → P-b
        elim-a (#a   p)      = h₀-a  p
        elim-a (#ba c co p) = h₀-ba c {co} (elim-b co) p
        elim-b (#ab c co p) = h₀-ab c {co} (elim-a co) p
