
{-# OPTIONS --without-K #-}

open import Base

module Homotopy.VanKampen.CodeTailFlip {i}
  (C A B : Set i) (f : C → A) (g : C → B) (c : C) where

  open import Homotopy.Truncation
  open import Spaces.Pi0PathSpace

  module TailFlipLemmaPack1 {i}
    (C A B : Set i) (f : C → A) (g : C → B) (c : C) where

    -- Code from A.
    open import Homotopy.VanKampen.CodeHeadMerge C A B f g (f c) hiding (P)
    -- Code from B. Code flipped. F for `flipped'.
    import Homotopy.VanKampen.CodeHeadMerge C B A g f (g c) as F hiding (P)

    aa⇒ba : ∀ {a₂} → code-a a₂ → F.code-b a₂
    ab⇒bb : ∀ {b₂} → code-b b₂ → F.code-a b₂
    ap⇒bp-split : (∀ {a₂} → code-a a₂ → F.code-b a₂)
                × (∀ {b₂} → code-b b₂ → F.code-a b₂)

    aa⇒ba = π₁ ap⇒bp-split
    ab⇒bb = π₂ ap⇒bp-split

    ap⇒bp-split = code-rec-nondep
                    F.code-b ⦃ λ _ → F.code-b-is-set ⦄
                    F.code-a ⦃ λ _ → F.code-a-is-set ⦄
                    h₀-a h₀-ba h₀-ab h₁-a h₁-ba h₁-ab
      where
        h₀-a : ∀ {a₂} (p : f c ≡₀ a₂) → F.code-b a₂
        h₀-a {a₂} p = F.ab c (F.a (refl₀ _)) p

        h₀-ba : ∀ {a₂} c₂ {co : code-b (g c₂)} → F.code-a (g c₂) → f c₂ ≡₀ a₂ → F.code-b a₂
        h₀-ba c₂ pco p = F.ab c₂ pco p

        h₀-ab : ∀ {b₂} c₂ {co : code-a (f c₂)} → F.code-b (f c₂) → g c₂ ≡₀ b₂ → F.code-a b₂
        h₀-ab c₂ pco p = F.ba c₂ pco p

        abstract
          h₁-a : ∀ {a₂} c₂ (p₁ : f c ≡₀ f c₂) (p₂ : f c₂ ≡₀ a₂) →
              (h₀-ba c₂ {⟧a p₁ a⟦ c₂ ⟧b refl₀ _}
                (h₀-ab c₂ {⟧a p₁} (h₀-a p₁) (refl₀ _)) p₂)
            ≡ h₀-a (p₁ ∘₀ p₂)
          h₁-a {a₂} c₂ p₁ p₂ =
            F.⟧a refl₀ _ F.a⟦ c ⟧b p₁ F.b⟦ c₂ ⟧a refl₀ _ F.a⟦ c₂ ⟧b p₂
              ≡⟨ F.code-ab-refl₀ c (F.⟧a refl₀ _) c₂ _ p₂ ⟩∎
            F.⟧a refl₀ _ F.a⟦ c ⟧b p₁ ∘₀ p₂
              ∎

        abstract
          h₁-ba : ∀ {a₂} c₁ {co : code-b (g c₁)} (pco : F.code-a (g c₁)) c₂ p₁ (p₂ : _ ≡₀ a₂) →
                (h₀-ba c₂ {co b⟦ c₁ ⟧a p₁ a⟦ c₂ ⟧b refl₀ _}
                  (h₀-ab c₂ {co b⟦ c₁ ⟧a p₁}
                    (h₀-ba c₁ {co} pco p₁)
                    (refl₀ _))
                  p₂)
              ≡ (h₀-ba c₁ {co} pco (p₁ ∘₀ p₂))
          h₁-ba c₁ {co} pco c₂ p₁ p₂ =
            pco F.a⟦ c₁ ⟧b p₁ F.b⟦ c₂ ⟧a refl₀ _ F.a⟦ c₂ ⟧b p₂
              ≡⟨ F.code-ab-refl₀ c₁ pco c₂ _ p₂ ⟩∎
            pco F.a⟦ c₁ ⟧b p₁ ∘₀ p₂
              ∎

        abstract
          h₁-ab : ∀ {b₂} c₁ {co : code-a (f c₁)} (pco : F.code-b (f c₁)) c₂ p₁ (p₂ : _ ≡₀ b₂) →
                (h₀-ab c₂ {co a⟦ c₁ ⟧b p₁ b⟦ c₂ ⟧a refl₀ _}
                  (h₀-ba c₂ {co a⟦ c₁ ⟧b p₁}
                    (h₀-ab c₁ {co} pco p₁)
                    (refl₀ _))
                  p₂)
              ≡ (h₀-ab c₁ {co} pco (p₁ ∘₀ p₂))
          h₁-ab c₁ {co} pco c₂ p₁ p₂ =
            pco F.b⟦ c₁ ⟧a p₁ F.a⟦ c₂ ⟧b refl₀ _ F.b⟦ c₂ ⟧a p₂
              ≡⟨ F.code-ba-refl₀ c₁ pco c₂ _ p₂ ⟩∎
            pco F.b⟦ c₁ ⟧a p₁ ∘₀ p₂
              ∎

  module TailFlipLemmaPack2 {i}
    (C A B : Set i) (f : C → A) (g : C → B) (c : C) where

    -- Code from A.
    open import Homotopy.VanKampen.CodeHeadMerge C A B f g (f c) hiding (P)
    open TailFlipLemmaPack1 C A B f g c public
    -- Code from B. Code flipped. F for `flipped'.
    private
      module F where
        open import Homotopy.VanKampen.CodeHeadMerge C B A g f (g c) public hiding (P)
        open TailFlipLemmaPack1 C B A g f c public

    aba-glue-code-split : (∀ {a₂} (co : code-a a₂) → F.ab⇒bb (aa⇒ba co) ≡ co)
                        × (∀ {b₂} (co : code-b b₂) → F.aa⇒ba (ab⇒bb co) ≡ co)
    aba-glue-code-a : ∀ {a₂} (co : code-a a₂) → F.ab⇒bb (aa⇒ba co) ≡ co
    aba-glue-code-b : ∀ {b₂} (co : code-b b₂) → F.aa⇒ba (ab⇒bb co) ≡ co

    aba-glue-code-a = π₁ aba-glue-code-split
    aba-glue-code-b = π₂ aba-glue-code-split

    aba-glue-code-split = code-rec
      (λ {a} co → F.ab⇒bb (aa⇒ba co) ≡ co)
      ⦃ λ _ → ≡-is-set code-a-is-set ⦄
      (λ {b} co → F.aa⇒ba (ab⇒bb co) ≡ co)
      ⦃ λ _ → ≡-is-set code-b-is-set ⦄
      (λ p →
        ⟧a refl₀ _ a⟦ c ⟧b refl₀ _ b⟦ c ⟧a p
            ≡⟨ code-a-refl₀ c (refl₀ _ ) p ⟩
        ⟧a refl₀ _ ∘₀ p
            ≡⟨ ap (λ x → ⟧a x) $ refl₀-left-unit p ⟩∎
        ⟧a p
            ∎)
      (λ c₁ {co} eq p → ap (λ x → x b⟦ c₁ ⟧a p) eq)
      (λ c₁ {co} eq p → ap (λ x → x a⟦ c₁ ⟧b p) eq)
      (λ _ _ _ → code-has-all-cells₂-a _ _)
      (λ _ _ _ _ _ → code-has-all-cells₂-a _ _)
      (λ _ _ _ _ _ → code-has-all-cells₂-b _ _)

  module TailFlipLemmaPack3 {i}
    (C A B : Set i) (f : C → A) (g : C → B) (c : C) where

    -- Code from A.
    open import Homotopy.VanKampen.CodeHeadMerge C A B f g (f c) hiding (P)
    open TailFlipLemmaPack2 C A B f g c public
    -- Code from B. Code flipped. F for `flipped'.
    private
      module F where
        open import Homotopy.VanKampen.CodeHeadMerge C B A g f (g c) public hiding (P)
        open TailFlipLemmaPack2 C B A g f c public

    open import Homotopy.PushoutDef
    P : Set i
    P = pushout (diag A , B , C , f , g)

    flipped-code : P → Set i
    flipped-code = F.code ◯ pushout-flip

    private
      -- not sure if this should be put into Paths.agda
      trans-app→app-trans : ∀ {i} {A : Set i} {j k} (B : A → Set j) (P : A → Set k)
        {b c : A} (p : b ≡ c) (q : B b → P b) (a : B b)
        → transport (λ x → B x → P x) p q (transport B p a)
          ≡ transport P p (q a)
      trans-app→app-trans B P (refl _) q a = refl _

      -- not sure if this should be put into Paths.agda
      trans-app→app : ∀ {i} {A : Set i} {j k} (B : A → Set j) (P : A → Set k)
        {b c : A} (p : b ≡ c) (q : B b → P b) (a : B c)
        → transport (λ x → B x → P x) p q a
          ≡ transport P p (q $ transport B (! p) a)
      trans-app→app B P (refl _) q a = refl _

    -- Because of the projection, this requires a nested induction
    -- or τ-extend.
    aa⇒ba-b⇒a′ : ∀ c₂ {b₁} (co : code-b b₁) (q : b₁ ≡ g c₂)
                 → aa⇒ba (b⇒a′ c₂ co q)
                 ≡ F.a⇒b c₂ (ab⇒bb $ transport code-b q co)
    aa⇒ba-b⇒a′ c₂ = code-rec-b
      (λ {b₁} co → (q : b₁ ≡ g c₂)
          → aa⇒ba (b⇒a′ c₂ co q)
          ≡ F.a⇒b c₂ (ab⇒bb $ transport code-b q co))
      ⦃ λ _ → Π-is-set λ _ → ≡-is-set F.code-b-is-set ⦄
      (λ c₁ co p q → refl _)
      (λ _ _ _ _ _ → funext λ _ → F.code-has-all-cells₂-b _ _)

    ap⇒bp : ∀ p → code p → flipped-code p
    ap⇒bp = pushout-rec (λ p → code p → flipped-code p)
      (λ _ → aa⇒ba)
      (λ _ → ab⇒bb)
      (λ c₂ → funext λ co →
        transport (λ p → code p → flipped-code p) (glue c₂) aa⇒ba co
            ≡⟨ trans-app→app code flipped-code (glue c₂) aa⇒ba co ⟩
        transport flipped-code (glue c₂)
          (aa⇒ba $ transport code (! $ glue c₂) co)
            ≡⟨ ap (λ x → transport flipped-code (glue c₂) $ aa⇒ba x)
                $ trans-!glue c₂ co ⟩
        transport flipped-code (glue c₂) (aa⇒ba $ b⇒a c₂ co)
            ≡⟨ ap (transport flipped-code (glue c₂)) $ aa⇒ba-b⇒a′ c₂ co (refl _) ⟩
        transport flipped-code (glue c₂) (F.a⇒b c₂ $ ab⇒bb co)
            ≡⟨ ! $ trans-ap {P = F.code} pushout-flip (glue c₂)
                 $ F.a⇒b c₂ $ ab⇒bb co ⟩
        transport F.code (ap pushout-flip $ glue c₂) (F.a⇒b c₂ $ ab⇒bb co)
            ≡⟨ ap (λ x → transport F.code x $ F.a⇒b c₂ $ ab⇒bb co)
                  $ pushout-β-glue-nondep _ right left (! ◯ glue) c₂ ⟩
        transport F.code (! $ glue c₂) (F.a⇒b c₂ $ ab⇒bb co)
            ≡⟨ F.trans-!glue c₂ (F.a⇒b c₂ $ ab⇒bb co) ⟩
        F.b⇒a c₂ (F.a⇒b c₂ $ ab⇒bb co)
            ≡⟨ F.code-glue-aba c₂ _ ⟩∎
        ab⇒bb co
            ∎)

  module TailFlipLemmaPack4 {i}
    (C A B : Set i) (f : C → A) (g : C → B) (c : C) where

    -- Code from A.
    open import Homotopy.VanKampen.CodeHeadMerge C A B f g (f c) hiding (P)
    open TailFlipLemmaPack3 C A B f g c public
    -- Code from B. Code flipped. F for `flipped'.
    private
      module F where
        open import Homotopy.VanKampen.CodeHeadMerge C B A g f (g c) public hiding (P)
        open TailFlipLemmaPack3 C B A g f c public

    open import Homotopy.PushoutDef

    bp⇒ap : ∀ p → flipped-code p → code p
    bp⇒ap p = transport
                (λ x → flipped-code p → code x)
                (pushout-flip-flip p)
                (F.ap⇒bp (pushout-flip p))

    open import HLevelBis
    private
      Laba : P → Set i
      Laba = λ p → ∀ (co : code p) → bp⇒ap p (ap⇒bp p co) ≡ co
    abstract
      ap⇒bp⇒ap : ∀ p → Laba p
      ap⇒bp⇒ap = pushout-rec Laba
        (λ _ → aba-glue-code-a)
        (λ _ → aba-glue-code-b)
        (λ _ → funext λ _ → prop-has-all-paths (code-b-is-set _ _) _ _)

    private
      Lbab : P → Set i
      Lbab = λ p → ∀ (co : flipped-code p) → ap⇒bp p (bp⇒ap p co) ≡ co
    abstract
      bp⇒ap⇒bp : ∀ p → Lbab p
      bp⇒ap⇒bp = pushout-rec Lbab
        (λ _ → F.aba-glue-code-b)
        (λ _ → F.aba-glue-code-a)
        (λ _ → funext λ _ → prop-has-all-paths (F.code-a-is-set _ _) _ _)

  open TailFlipLemmaPack4 C A B f g c public
