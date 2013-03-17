
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
      (λ p → F.⟧a refl₀ _ F.a⟦ c ⟧b p)
      (λ c₂ pco p → F.ab c₂ pco p)
      (λ c₂ pco p → F.ba c₂ pco p)
      (λ c₂ p₁ p₂ →
          F.⟧a refl₀ _ F.a⟦ c ⟧b p₁ F.b⟦ c₂ ⟧a refl₀ _ F.a⟦ c₂ ⟧b p₂
            ≡⟨ F.code-ab-refl₀ c (F.⟧a refl₀ _) c₂ _ p₂ ⟩∎
          F.⟧a refl₀ _ F.a⟦ c ⟧b p₁ ∘₀ p₂
            ∎)
      (λ c₁ pco c₂ p₁ p₂ →
          pco F.a⟦ c₁ ⟧b p₁ F.b⟦ c₂ ⟧a refl₀ _ F.a⟦ c₂ ⟧b p₂
            ≡⟨ F.code-ab-refl₀ c₁ pco c₂ _ p₂ ⟩∎
          pco F.a⟦ c₁ ⟧b p₁ ∘₀ p₂
            ∎)
      (λ c₁ pco c₂ p₁ p₂ →
          pco F.b⟦ c₁ ⟧a p₁ F.a⟦ c₂ ⟧b refl₀ _ F.b⟦ c₂ ⟧a p₂
            ≡⟨ F.code-ba-refl₀ c₁ pco c₂ _ p₂ ⟩∎
          pco F.b⟦ c₁ ⟧a p₁ ∘₀ p₂
            ∎)

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
      ab-to′-aa-to-ab : ∀ c₂ {b₁} (co : code-b b₁) (q : b₁ ≡ g c₂)
        → aa⇒ba (b⇒a′ c₂ co q)
        ≡ F.a⇒b c₂ (ab⇒bb $ transport code-b q co)
      ab-to′-aa-to-ab c₂ = code-b-rec
        (λ {b₁} co → (q : b₁ ≡ g c₂)
            → aa⇒ba (b⇒a′ c₂ co q)
            ≡ F.a⇒b c₂ (ab⇒bb $ transport code-b q co))
        ⦃ λ _ → Π-is-set λ _ → ≡-is-set F.code-b-is-set ⦄
        (λ c₁ co p q → refl _)
        (λ _ _ _ _ _ → funext λ _ → F.code-has-all-cells₂-b _ _)

    ap⇒bp : ∀ {p} → code p → flipped-code p
    ap⇒bp {p} = pushout-rec
      (λ x → code x → flipped-code x)
      (λ _ → aa⇒ba)
      (λ _ → ab⇒bb)
      (λ c₂ → funext λ co →
        transport (λ p → code p → flipped-code p) (glue c₂) aa⇒ba co
            ≡⟨ trans-→ code flipped-code (glue c₂) aa⇒ba co ⟩
        transport flipped-code (glue c₂)
          (aa⇒ba $ transport code (! $ glue c₂) co)
            ≡⟨ ap (λ x → transport flipped-code (glue c₂) $ aa⇒ba x)
                $ trans-code-!glue c₂ co ⟩
        transport flipped-code (glue c₂) (aa⇒ba $ b⇒a c₂ co)
            ≡⟨ ap (transport flipped-code (glue c₂)) $ ab-to′-aa-to-ab c₂ co (refl _) ⟩
        transport flipped-code (glue c₂) (F.a⇒b c₂ $ ab⇒bb co)
            ≡⟨ ! $ trans-ap F.code pushout-flip (glue c₂)
                 $ F.a⇒b c₂ $ ab⇒bb co ⟩
        transport F.code (ap pushout-flip $ glue c₂) (F.a⇒b c₂ $ ab⇒bb co)
            ≡⟨ ap (λ x → transport F.code x $ F.a⇒b c₂ $ ab⇒bb co)
                  $ pushout-β-glue-nondep _ right left (! ◯ glue) c₂ ⟩
        transport F.code (! $ glue c₂) (F.a⇒b c₂ $ ab⇒bb co)
            ≡⟨ F.trans-code-!glue c₂ (F.a⇒b c₂ $ ab⇒bb co) ⟩
        F.b⇒a c₂ (F.a⇒b c₂ $ ab⇒bb co)
            ≡⟨ F.code-glue-aba c₂ _ ⟩∎
        ab⇒bb co
            ∎)
      p

  -- Nice interface
  module _ where
    private
      -- Code from A.
      module C where
        open import Homotopy.VanKampen.SplitCode C A B f g public
        open Pack3 A B f g public
      -- Code from B. Code flipped.
      module CF where
        open import Homotopy.VanKampen.SplitCode C B A g f public
        open Pack3 B A g f public

    P : Set i
    P = pushout (diag A , B , C , f , g)

    module _ where
      -- Things that can be directly imported
      open import Homotopy.VanKampen.SplitCode C A B f g public
        using () renaming
          ( code            to a-code
          ; code-a          to a-code-a
          ; code-b          to a-code-b
          ; code-rec        to a-code-rec
          ; code-rec-nondep to a-code-rec-nondep
          ; code-is-set     to a-code-is-set
          ; code-a-is-set   to a-code-a-is-set
          ; code-b-is-set   to a-code-b-is-set
          )

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

    module _ where
      -- Things that can be directly imported
      open import Homotopy.VanKampen.SplitCode C B A g f public
        using () renaming
          ( code-a          to b-code-b
          ; code-b          to b-code-a
          ; code-rec        to b-code-rec
          ; code-rec-nondep to b-code-rec-nondep
          ; code-a-is-set   to b-code-b-is-set
          ; code-b-is-set   to b-code-a-is-set
          )

      b-code : B → P → Set i
      b-code b = CF.code b ◯ pushout-flip

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

      b-code-is-set : ∀ b₁ p₂ → is-set (b-code b₁ p₂)
      b-code-is-set b₁ = CF.code-is-set b₁ ◯ pushout-flip

    -- Head flipping
    aa⇒ab : ∀ {a} c → a-code-a a (f c) → a-code-b a (g c)
    aa⇒ab {a} = C.a⇒b a

    ab⇒aa : ∀ {a} c → a-code-b a (g c) → a-code-a a (f c)
    ab⇒aa {a} = C.b⇒a a

    ba⇒bb : ∀ {b} c → b-code-a b (f c) → b-code-b b (g c)
    ba⇒bb {b} = CF.b⇒a b

    bb⇒ba : ∀ {b} c → b-code-b b (g c) → b-code-a b (f c)
    bb⇒ba {b} = CF.a⇒b b

    -- Tail flipping
    aa⇒ba : ∀ c {a} → a-code-a (f c) a → b-code-a (g c) a
    aa⇒ba = C.aa⇒ba

    ab⇒bb : ∀ c {b} → a-code-b (f c) b → b-code-b (g c) b
    ab⇒bb = C.ab⇒bb

    ba⇒aa : ∀ c {a} → b-code-a (g c) a → a-code-a (f c) a
    ba⇒aa = CF.ab⇒bb

    bb⇒ab : ∀ c {b} → b-code-b (g c) b → a-code-b (f c) b
    bb⇒ab = CF.aa⇒ba

    ap⇒bp : ∀ c {p} → a-code (f c) p → b-code (g c) p
    ap⇒bp c {p} = C.ap⇒bp c {p}

    bp⇒ap : ∀ c {p} → b-code (g c) p → a-code (f c) p
    bp⇒ap c {p} = transport
      (λ x → b-code (g c) p → a-code (f c) x)
      (pushout-flip-flip p)
      (CF.ap⇒bp c {pushout-flip p})

    private
      Laba : C → P → Set i
      Laba = λ c p → ∀ (co : a-code (f c) p) → bp⇒ap c {p} (ap⇒bp c {p} co) ≡ co
    abstract
      aba-glue-code : ∀ c {p} → Laba c p
      aba-glue-code c {p} = pushout-rec (Laba c)
        (λ _ → C.aba-glue-code-a c)
        (λ _ → C.aba-glue-code-b c)
        (λ _ → funext λ _ → prop-has-all-paths (a-code-b-is-set (f c) _ _) _ _)
        p

    private
      Lbab : C → P → Set i
      Lbab = λ c p → ∀ (co : b-code (g c) p) → ap⇒bp c {p} (bp⇒ap c {p} co) ≡ co
    abstract
      bab-glue-code : ∀ c {p} → Lbab c p
      bab-glue-code c {p} = pushout-rec (Lbab c)
        (λ _ → CF.aba-glue-code-b c)
        (λ _ → CF.aba-glue-code-a c)
        (λ _ → funext λ _ → prop-has-all-paths (CF.code-a-is-set (g c) _ _) _ _)
        p

    glue-code : ∀ c → a-code (f c) ≡ b-code (g c)
    private
      glue-code-pointwise : ∀ c p → a-code (f c) p ≡ b-code (g c) p
      glue-code-pointwise-eq : ∀ c p → a-code (f c) p ≃ b-code (g c) p

    glue-code c = funext $ glue-code-pointwise c
    glue-code-pointwise c p = eq-to-path $ glue-code-pointwise-eq c p
    glue-code-pointwise-eq c p = ap⇒bp c {p} , iso-is-eq
      (ap⇒bp c {p}) (bp⇒ap c {p}) (bab-glue-code c {p}) (aba-glue-code c {p})

    code : P → P → Set i
    code = pushout-rec-nondep (P → Set i) a-code b-code glue-code

    open import HLevelBis
    abstract
      code-is-set : ∀ p₁ p₂ → is-set (code p₁ p₂)
      code-is-set = pushout-rec
        (λ p₁ → ∀ p₂ → is-set $ code p₁ p₂)
        a-code-is-set
        b-code-is-set
        (λ _ → prop-has-all-paths (Π-is-prop λ _ → is-set-is-prop) _ _)

    -- Useful lemma
    trans-a-code-glue : ∀ {a₁} c₂ co → transport (a-code a₁) (glue c₂) co ≡ aa⇒ab c₂ co
    trans-a-code-glue {a₁} = C.trans-code-glue a₁

    trans-a-code-!glue : ∀ {a₁} c₂ co → transport (a-code a₁) (! $ glue c₂) co ≡ ab⇒aa c₂ co
    trans-a-code-!glue {a₁} = C.trans-code-!glue a₁

    trans-b-code-!glue : ∀ {b₁} c₂ co → transport (b-code b₁) (! (glue c₂)) co ≡ bb⇒ba c₂ co
    trans-b-code-!glue {b₁} c₂ co =
      transport (b-code b₁) (! (glue c₂)) co
          ≡⟨ ! $ trans-ap (CF.code b₁) pushout-flip (! (glue c₂)) co ⟩
      transport (CF.code b₁) (ap pushout-flip (! (glue c₂))) co
          ≡⟨ ap (λ x → transport (CF.code b₁) x co)
                $ pushout-β-!glue-nondep _ right left (! ◯ glue) c₂ ⟩
      transport (CF.code b₁) (! (! (glue c₂))) co
          ≡⟨ ap (λ x → transport (CF.code b₁) x co)
                $ opposite-opposite $ glue c₂ ⟩
      transport (CF.code b₁) (glue c₂) co
          ≡⟨ CF.trans-code-glue b₁ c₂ co ⟩∎
      bb⇒ba c₂ co
          ∎

    trans-glue-code : ∀ c {p} (co : a-code (f c) p)
      → transport (λ x → code x p) (glue c) co
      ≡ ap⇒bp c {p} co
    trans-glue-code c {p} co =
        transport (λ x → code x p) (glue c) co
            ≡⟨ ! $ trans-ap (λ f → f p) code (glue c) co ⟩
        transport (λ f → f p) (ap code (glue c)) co
            ≡⟨ ap (λ x →  transport (λ f → f p) x co)
                $ pushout-β-glue-nondep (P → Set i) a-code b-code glue-code c ⟩
        transport (λ f → f p) (glue-code c) co
            ≡⟨ ! $ trans-ap (λ X → X) (λ f → f p) (glue-code c) co ⟩
        transport (λ X → X) (happly (glue-code c) p) co
            ≡⟨ ap (λ x → transport (λ X → X) (x p) co) $ happly-funext $ glue-code-pointwise c ⟩
        transport (λ X → X) (glue-code-pointwise c p) co
            ≡⟨ trans-id-eq-to-path (glue-code-pointwise-eq c p) co ⟩∎
        ap⇒bp c {p} co
            ∎

    trans-!glue-code : ∀ c {p} (co : b-code (g c) p)
      → transport (λ x → code x p) (! $ glue c) co
      ≡ bp⇒ap c {p} co
    trans-!glue-code c {p} co =
      move!-transp-right (λ x → code x p) (glue c) co (bp⇒ap c {p} co)
        $ ! $
          transport (λ x → code x p) (glue c) (bp⇒ap c {p} co)
            ≡⟨ trans-glue-code c {p} (bp⇒ap c {p} co) ⟩
          ap⇒bp c {p} (bp⇒ap c {p} co)
            ≡⟨ bab-glue-code c {p} co ⟩∎
          co
            ∎
