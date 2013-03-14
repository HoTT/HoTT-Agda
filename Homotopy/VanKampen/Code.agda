{-# OPTIONS --without-K #-}

open import Base

{-
  The truncated representation for paths in a pushout.
  This is a combintion of two instances of OneSidedCode.
  See OneSidedCode.agda.

       g
    C---->B
    |     |
   f|  ~  |right
    v     v
    A---->P
     left

  This is for formalizing the van Kampen thereom.
-}

module Homotopy.VanKampen.Code {i}
  (C A B : Set i) (f : C → A) (g : C → B) where

  open import Spaces.Pi0PathSpace
  open import Homotopy.PushoutDef

  -- Code from A.
  module C where
    open import Homotopy.VanKampen.CodeHeadMerge C A B f g public hiding (P)
    open import Homotopy.VanKampen.CodeTailFlip C A B f g public hiding (P)
  -- Code from B. Code flipped.
  module CF where
    open import Homotopy.VanKampen.CodeHeadMerge C B A g f public hiding (P)
    open import Homotopy.VanKampen.CodeTailFlip C B A g f public hiding (P)

  P : Set i
  P = pushout (diag A , B , C , f , g)

  a-code : A → P → Set i
  a-code = C.code

  a-code-a : A → A → Set i
  a-code-a = C.code-a

  a-code-b : A → B → Set i
  a-code-b = C.code-b

  a-a : ∀ {a₁} {a₂} → a₁ ≡₀ a₂ → a-code-a a₁ a₂
  a-a = C.a _

  infixl 6 a-a
  syntax a-a co = ⟧a co

  a-ba : ∀ {a₁} {a₂} c → a-code-b a₁ (g c) → f c ≡₀ a₂ → a-code-a a₁ a₂
  a-ba = C.ba _

  infixl 6 a-ba
  syntax a-ba c co p = co ab⟦ c ⟧a p

  a-ab : ∀ {a₁} {b₂} c → a-code-a a₁ (f c) → g c ≡₀ b₂ → a-code-b a₁ b₂
  a-ab = C.ab _

  infixl 6 a-ab
  syntax a-ab c co p = co aa⟦ c ⟧b p

  b-code : B → P → Set i
  b-code b = CF.code b ◯ pushout-flip

  b-code-a : B → A → Set i
  b-code-a = CF.code-b

  b-code-b : B → B → Set i
  b-code-b = CF.code-a

  b-b : ∀ {b₁} {b₂} → b₁ ≡₀ b₂ → b-code-b b₁ b₂
  b-b = CF.a _

  infixl 6 b-b
  syntax b-b co = ⟧b co

  b-ab : ∀ {b₁} {b₂} c → b-code-a b₁ (f c) → g c ≡₀ b₂ → b-code-b b₁ b₂
  b-ab = CF.ba _

  infixl 6 b-ab
  syntax b-ab c co p = co ba⟦ c ⟧b p

  b-ba : ∀ {b₁} {a₂} c → b-code-b b₁ (g c) → f c ≡₀ a₂ → b-code-a b₁ a₂
  b-ba = CF.ab _

  infixl 6 b-ba
  syntax b-ba c co p = co bb⟦ c ⟧a p

  a-code-a-refl₀ : ∀ {a₁} {a₂} c (p₁ : a₁ ≡₀ _) (p₂ : _ ≡₀ a₂)
    → ⟧a p₁ aa⟦ c ⟧b refl₀ _ ab⟦ c ⟧a p₂
    ≡ ⟧a p₁             ∘₀            p₂
  a-code-a-refl₀ = C.code-a-refl₀ _

  a-code-ba-refl₀ : ∀ {a₁} {a₂} c₁ (co : a-code-b a₁ _) c₂ p₁ (p₂ : _ ≡₀ a₂)
    → co ab⟦ c₁ ⟧a p₁ aa⟦ c₂ ⟧b refl₀ _ ab⟦ c₂ ⟧a p₂
    ≡ co ab⟦ c₁ ⟧a p₁              ∘₀             p₂
  a-code-ba-refl₀ = C.code-ba-refl₀ _

  a-code-ab-refl₀ : ∀ {a₁} {b₂} c₁ (co : a-code-a a₁ _) c₂ p₁ (p₂ : _ ≡₀ b₂)
    → co aa⟦ c₁ ⟧b p₁ ab⟦ c₂ ⟧a refl₀ _ aa⟦ c₂ ⟧b p₂
    ≡ co aa⟦ c₁ ⟧b p₁              ∘₀             p₂
  a-code-ab-refl₀ = C.code-ab-refl₀ _

  b-code-b-refl₀ : ∀ {b₁} {b₂} c (p₁ : b₁ ≡₀ _) (p₂ : _ ≡₀ b₂)
    → ⟧b p₁ bb⟦ c ⟧a refl₀ _ ba⟦ c ⟧b p₂
    ≡ ⟧b p₁             ∘₀            p₂
  b-code-b-refl₀ = CF.code-a-refl₀ _

  b-code-ab-refl₀ : ∀ {b₁} {b₂} c₁ (co : b-code-a b₁ _) c₂ p₁ (p₂ : _ ≡₀ b₂)
    → co ba⟦ c₁ ⟧b p₁ bb⟦ c₂ ⟧a refl₀ _ ba⟦ c₂ ⟧b p₂
    ≡ co ba⟦ c₁ ⟧b p₁              ∘₀             p₂
  b-code-ab-refl₀ = CF.code-ba-refl₀ _

  b-code-ba-refl₀ : ∀ {b₁} {a₂} c₁ (co : b-code-b b₁ _) c₂ p₁ (p₂ : _ ≡₀ a₂)
    → co bb⟦ c₁ ⟧a p₁ ba⟦ c₂ ⟧b refl₀ _ bb⟦ c₂ ⟧a p₂
    ≡ co bb⟦ c₁ ⟧a p₁              ∘₀             p₂
  b-code-ba-refl₀ = CF.code-ab-refl₀ _

  -- tail flipping
  aa⇒ba : ∀ {c} {a} → a-code-a (f c) a → b-code-a (g c) a
  aa⇒ba = C.aa⇒ba _

  ab⇒bb : ∀ {c} {b} → a-code-b (f c) b → b-code-b (g c) b
  ab⇒bb = C.ab⇒bb _

  ba⇒aa : ∀ {c} {a} → b-code-a (g c) a → a-code-a (f c) a
  ba⇒aa = CF.ab⇒bb _

  bb⇒ab : ∀ {c} {b} → b-code-b (g c) b → a-code-b (f c) b
  bb⇒ab = CF.aa⇒ba _

  glue-code-a : ∀ c → (∀ {a} co → ba⇒aa (aa⇒ba co) ≡ co)
                    × (∀ {b} co → bb⇒ab (ab⇒bb co) ≡ co)
  glue-code-a c = C.code-rec (f c)
    (λ {a} co → ba⇒aa (aa⇒ba co) ≡ co)
    ⦃ λ _ → ≡-is-set $ C.code-a-is-set _ ⦄
    (λ {b} co → bb⇒ab (ab⇒bb co) ≡ co)
    ⦃ λ _ → ≡-is-set $ C.code-b-is-set _ ⦄
    (λ p →
      ⟧a refl₀ _ aa⟦ c ⟧b refl₀ _ ab⟦ c ⟧a p
          ≡⟨ a-code-a-refl₀ c (refl₀ _ ) p ⟩
      ⟧a refl₀ _ ∘₀ p
          ≡⟨ ap (λ x → ⟧a x) $ refl₀-left-unit p ⟩∎
      ⟧a p
          ∎)
    (λ c₁ {co} eq p → ap (λ x → x ab⟦ c₁ ⟧a p) eq)
    (λ c₁ {co} eq p → ap (λ x → x aa⟦ c₁ ⟧b p) eq)
    (λ _ _ _ → C.code-has-all-cells₂-a _ _ _)
    (λ _ _ _ _ _ → C.code-has-all-cells₂-a _ _ _)
    (λ _ _ _ _ _ → C.code-has-all-cells₂-b _ _ _)

  glue-code-b : ∀ c → (∀ {b} co → ab⇒bb (bb⇒ab co) ≡ co)
                    × (∀ {a} co → aa⇒ba (ba⇒aa co) ≡ co)
  glue-code-b c = CF.code-rec (g c)
    (λ {b} co → ab⇒bb (bb⇒ab co) ≡ co)
    ⦃ λ _ → ≡-is-set $ CF.code-a-is-set _ ⦄
    (λ {a} co → aa⇒ba (ba⇒aa co) ≡ co)
    ⦃ λ _ → ≡-is-set $ CF.code-b-is-set _ ⦄
    (λ p →
      ⟧b refl₀ _ bb⟦ c ⟧a refl₀ _ ba⟦ c ⟧b p
          ≡⟨ b-code-b-refl₀ c (refl₀ _) p ⟩
      ⟧b refl₀ _ ∘₀ p
          ≡⟨ ap (λ x → ⟧b x) $ refl₀-left-unit p ⟩∎
      ⟧b p
          ∎)
    (λ c₁ {co} eq p → ap (λ x → x ba⟦ c₁ ⟧b p) eq)
    (λ c₁ {co} eq p → ap (λ x → x bb⟦ c₁ ⟧a p) eq)
    (λ _ _ _ → CF.code-has-all-cells₂-a _ _ _)
    (λ _ _ _ _ _ → CF.code-has-all-cells₂-a _ _ _)
    (λ _ _ _ _ _ → CF.code-has-all-cells₂-b _ _ _)

  ap⇒bp : ∀ c p → a-code (f c) p → b-code (g c) p
  ap⇒bp = C.ap⇒bp

  bp⇒ap : ∀ c p → b-code (g c) p → a-code (f c) p
  bp⇒ap = C.bp⇒ap

  code : P → P → Set i
  code = pushout-rec-nondep (P → Set i) a-code b-code lemma-glue
    where
      lemma-glue : ∀ c → a-code (f c) ≡ b-code (g c)
      lemma-glue-eq : ∀ c p → a-code (f c) p ≃ b-code (g c) p

      lemma-glue c = funext $ eq-to-path ◯ lemma-glue-eq c
      lemma-glue-eq c p = C.ap⇒bp c p , iso-is-eq
        (ap⇒bp c p)
        (bp⇒ap c p)
        (C.bp⇒ap⇒bp c p)
        (C.ap⇒bp⇒ap c p)

