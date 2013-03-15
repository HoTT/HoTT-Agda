
{-# OPTIONS --without-K #-}

open import Base

module Homotopy.VanKampen.Code {i}
  (C A B : Set i) (f : C → A) (g : C → B) where

  open import Homotopy.PushoutDef
  open import Homotopy.Truncation
  open import Spaces.Pi0Paths

  module Pack1 (A B : Set i) (f : C → A) (g : C → B) (c : C) where
    -- Code from A.
    open import Homotopy.VanKampen.SplitCode C A B f g (f c)
    -- Code from B. F for `flipped'.
    import Homotopy.VanKampen.SplitCode C B A g f (g c) as F

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
        h₀-a {a₂} p = F.⟧a refl₀ _ F.a⟦ c ⟧b p

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

  module Pack2 (A B : Set i) (f : C → A) (g : C → B) (c : C) where
    -- Code from A.
    open Pack1 A B f g c public
    open import Homotopy.VanKampen.SplitCode C A B f g (f c)
    -- Code from B. F for `flipped'.
    private
      module F where
        open import Homotopy.VanKampen.SplitCode C B A g f (g c) public
        open Pack1 B A g f c public

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

  module Pack3 (A B : Set i) (f : C → A) (g : C → B) (c : C) where

    -- Code from A.
    open Pack2 A B f g c public
    open import Homotopy.VanKampen.SplitCode C A B f g (f c)
    -- Code from B. F for `flipped'.
    private
      module F where
        open import Homotopy.VanKampen.SplitCode C B A g f (g c) public hiding (P)
        open Pack2 B A g f c public

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

  module Pack4 (A B : Set i) (f : C → A) (g : C → B) (c : C) where

    -- Code from A.
    open import Homotopy.VanKampen.SplitCode C A B f g (f c)
    open Pack3 A B f g c public
    -- Code from B. F for `flipped'.
    private
      module F where
        open import Homotopy.VanKampen.SplitCode C B A g f (g c) public
        open Pack3 B A g f c public

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

  -- Nice interface
  module _ where
    -- Code from A.
    module C where
      open import Homotopy.VanKampen.SplitCode C A B f g public
      open Pack4 A B f g public
    -- Code from B. Code flipped.
    module CF where
      open import Homotopy.VanKampen.SplitCode C B A g f public
      open Pack4 B A g f public

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

    -- head flipping
    aa⇒ab : ∀ {a} {c} → a-code-a a (f c) → a-code-b a (g c)
    aa⇒ab {a} {c} = C.a⇒b a c

    ab⇒aa : ∀ {a} {c} → a-code-b a (g c) → a-code-a a (f c)
    ab⇒aa {a} {c} = C.b⇒a a c

    ba⇒bb : ∀ {b} {c} → b-code-a b (f c) → b-code-b b (g c)
    ba⇒bb {b} {c} = CF.b⇒a b c

    bb⇒ba : ∀ {b} {c} → b-code-b b (g c) → b-code-a b (f c)
    bb⇒ba {b} {c} = CF.a⇒b b c

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

    ap⇒bp : ∀ c {p} → a-code (f c) p → b-code (g c) p
    ap⇒bp c {p} = C.ap⇒bp c p

    bp⇒ap : ∀ c {p} → b-code (g c) p → a-code (f c) p
    bp⇒ap c {p} = C.bp⇒ap c p

    glue-code : ∀ c → a-code (f c) ≡ b-code (g c)
    glue-code-pointwise : ∀ c p → a-code (f c) p ≡ b-code (g c) p
    glue-code-pointwise-eq : ∀ c p → a-code (f c) p ≃ b-code (g c) p

    glue-code c = funext $ glue-code-pointwise c
    glue-code-pointwise c p = eq-to-path $ glue-code-pointwise-eq c p
    glue-code-pointwise-eq c p = C.ap⇒bp c p , iso-is-eq
      (ap⇒bp c {p}) (bp⇒ap c {p}) (C.bp⇒ap⇒bp c p) (C.ap⇒bp⇒ap c p)

    code : P → P → Set i
    code = pushout-rec-nondep (P → Set i) a-code b-code glue-code

    open import HLevelBis
    abstract
      code-is-set : ∀ {p₁ p₂} → is-set (code p₁ p₂)
      code-is-set {p₁} {p₂} = pushout-rec
        (λ p₁ → ∀ p₂ → is-set $ code p₁ p₂)
        (λ a → λ p₂ → C.code-is-set a {p₂})
        (λ b → λ p₂ → CF.code-is-set b {pushout-flip p₂})
        (λ _ → prop-has-all-paths (Π-is-prop λ _ → is-set-is-prop) _ _)
        p₁ p₂
