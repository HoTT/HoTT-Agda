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

  open import Homotopy.PushoutDef
  open import Homotopy.Truncation
  open import Spaces.Pi0Paths

  -- Definition.
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
    -- all-paths
    abstract
      code-has-all-cells₂-a : ∀ {a} {x y : code-a a} (p q : x ≡ y) → p ≡ q
      code-has-all-cells₂-a = prop-has-all-paths $ code-a-is-set _ _

      code-has-all-cells₂-b : ∀ {b} {x y : code-b b} (p q : x ≡ y) → p ≡ q
      code-has-all-cells₂-b = prop-has-all-paths $ code-b-is-set _ _

    -- Non-recursive recursor
    code-a-rec : ∀ {j}
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
    code-a-rec {j} P-a ⦃ P-a-is-set ⦄ h₀-a h₀-ba h₁-a h₁-ba = π₁ $ code-rec
      P-a ⦃ P-a-is-set ⦄
      (λ _ → unit) ⦃ λ _ → unit-is-set ⦄
      h₀-a
      (λ c {co} _ → h₀-ba c co)
      (λ _ _ _ → tt)
      h₁-a
      (λ c₁ {co} _ → h₁-ba c₁ co)
      (λ _ _ _ _ _ → prop-has-all-paths unit-is-prop _ _)

    code-b-rec : ∀ {j}
      (P-b : ∀ {b₂} → code-b b₂ → Set j) ⦃ _ : ∀ {b₂} co → is-set $ P-b {b₂} co ⦄
      (h₀-ab : ∀ {b₂} c co (p : _ ≡₀ b₂) → P-b (co a⟦ c ⟧b p))
      (h₁-ab : ∀ {b₂} c₁ co c₂ p₁ (p₂ : _ ≡₀ b₂) →
        transport P-b (code-ab-refl₀ c₁ co c₂ p₁ p₂)
          (h₀-ab c₂ (co a⟦ c₁ ⟧b p₁ b⟦ c₂ ⟧a refl₀ _) p₂)
        ≡ (h₀-ab c₁ co (p₁ ∘₀ p₂)))
      → (∀ {b₂} (co : code-b b₂) → P-b co)
    code-b-rec {j} P-b ⦃ P-b-is-set ⦄ h₀-ab h₁-ab = π₂ $ code-rec
      (λ _ → unit) ⦃ λ _ → unit-is-set ⦄
      P-b ⦃ P-b-is-set ⦄
      (λ _ → tt)
      (λ _ _ _ → tt)
      (λ c {co} _ → h₀-ab c co)
      (λ _ _ _ → prop-has-all-paths unit-is-prop _ _)
      (λ _ _ _ _ _ → prop-has-all-paths unit-is-prop _ _)
      (λ c₁ {co} _ → h₁-ab c₁ co)

  module _ where
    P : Set i
    P = pushout (diag A , B , C , f , g)

    -- Basic conversion
    a⇒b : ∀ c → code-a (f c) → code-b (g c)
    a⇒b c co = co a⟦ c ⟧b refl₀ _

    b⇒a : ∀ c → code-b (g c) → code-a (f c)
    b⇒a c co = co b⟦ c ⟧a refl₀ _

    -- Proof trick:
    --   Intentionally relax one end for induction
    --   but enable proper computation rules to reduce work.
    a⇒b′ : ∀ c {a₂} → code-a a₂ → a₂ ≡ f c → code-b (g c)
    a⇒b′ c co p = transport code-a p co a⟦ c ⟧b refl₀ _

    b⇒a′ : ∀ c {b₂} → code-b b₂ → b₂ ≡ g c → code-a (f c)
    b⇒a′ c co p = transport code-b p co b⟦ c ⟧a refl₀ _

    -- Useful lemma about transport and code
    trans-a : ∀ {y z} (q : y ≡ z) (p : a₁ ≡₀ y)
      → transport code-a q (a p) ≡ a (p ∘₀ proj q)
    trans-a (refl _) p = ap a (! (refl₀-right-unit p))

    trans-ba : ∀ {y z} (q : y ≡ z) c co (p : f c ≡₀ y)
      → transport code-a q (co b⟦ c ⟧a p) ≡ co b⟦ c ⟧a p ∘₀ proj q
    trans-ba (refl _) c co p = ap (ba c co) (! (refl₀-right-unit p))

    trans-ab : ∀ {y b} (q : y ≡ b) c co (p : g c ≡₀ y)
      → transport code-b q (co a⟦ c ⟧b p) ≡ co a⟦ c ⟧b p ∘₀ proj q
    trans-ab (refl _) c co p = ap (ab c co) (! (refl₀-right-unit p))

    -- Merge of two code types with respect to `flipped'
    private
      G-a = λ c {a₂} co → (q : a₂ ≡ f c)
        → b⇒a c (a⇒b′ c co q) ≡ transport code-a q co

      G-a-is-set : ∀ c {a₂} co → is-set (G-a c {a₂} co)
      G-a-is-set _ {a₂} co = Π-is-set λ _ → ≡-is-set code-a-is-set

      G-b = λ c {b₂} co → (q : b₂ ≡ g c)
        → a⇒b c (b⇒a′ c co q) ≡ transport code-b q co

      G-b-is-set : ∀ c {b₂} co → is-set (G-b c {b₂} co)
      G-b-is-set _ {b₂} co = Π-is-set λ _ → ≡-is-set code-b-is-set

    -- the head of the code
    code-glue : ∀ c → code-a (f c) ≡ code-b (g c)
    code-glue-aba : ∀ c (co : code-a (f c)) → b⇒a c (a⇒b c co) ≡ co
    code-glue-bab : ∀ c (co : code-b (g c)) → a⇒b c (b⇒a c co) ≡ co
    private
      code-glue-eq : ∀ c → code-a (f c) ≃ code-b (g c)
      code-glue-split : ∀ c
        → (∀ {a₂} co → G-a c {a₂} co)
        × (∀ {b₂} co → G-b c {b₂} co)

    code-glue-aba c co = π₁ (code-glue-split c) co $ refl _
    code-glue-bab c co = π₂ (code-glue-split c) co $ refl _
    code-glue-eq c = a⇒b c , iso-is-eq (a⇒b c) (b⇒a c) (code-glue-bab c) (code-glue-aba c)
    code-glue c = eq-to-path $ code-glue-eq c
    code-glue-split c = code-rec
      (G-a c) ⦃ G-a-is-set c ⦄
      (G-b c) ⦃ G-b-is-set c ⦄
      (λ p q →
        b⇒a c (a⇒b c $ transport code-a q (a p))
          ≡⟨ ap (b⇒a c ◯ a⇒b c) $ trans-a q _ ⟩
        b⇒a c (a⇒b c $ a (p ∘₀ proj q))
          ≡⟨ code-a-refl₀ _ _ _ ⟩
        a ((p ∘₀ proj q) ∘₀ refl₀ _)
          ≡⟨ ap a $ refl₀-right-unit _ ⟩
        a (p ∘₀ proj q)
          ≡⟨ ! $ trans-a q _ ⟩∎
        transport code-a q (a p)
          ∎)
      (λ c₁ {co} _ p q →
        b⇒a c (a⇒b c $ transport code-a q (ba c₁ co p))
          ≡⟨ ap (b⇒a c ◯ a⇒b c) $ trans-ba q c₁ co p ⟩
        b⇒a c (a⇒b c $ ba c₁ co (p ∘₀ proj q))
          ≡⟨ code-ba-refl₀ c₁ co _ _ (refl₀ _) ⟩
        ba c₁ co ((p ∘₀ proj q) ∘₀ refl₀ _)
          ≡⟨ ap (ba c₁ co) $ refl₀-right-unit _ ⟩
        ba c₁ co (p ∘₀ proj q)
          ≡⟨ ! $ trans-ba q c₁ co p ⟩∎
        transport code-a q (ba c₁ co p)
          ∎)
      (λ c₁ {co} _ p q →
        a⇒b c (b⇒a c $ transport code-b q (ab c₁ co p))
          ≡⟨ ap (a⇒b c ◯ b⇒a c) $ trans-ab q c₁ co p ⟩
        a⇒b c (b⇒a c $ ab c₁ co (p ∘₀ proj q))
          ≡⟨ code-ab-refl₀ c₁ co _ _ (refl₀ _) ⟩
        ab c₁ co ((p ∘₀ proj q) ∘₀ refl₀ _)
          ≡⟨ ap (ab c₁ co) $ refl₀-right-unit _ ⟩
        ab c₁ co (p ∘₀ proj q)
          ≡⟨ ! $ trans-ab q c₁ co p ⟩∎
        transport code-b q (ab c₁ co p)
          ∎)
      (λ _ _ _ → funext λ _ → code-has-all-cells₂-a _ _)
      (λ _ _ _ _ _ → funext λ _ → code-has-all-cells₂-a _ _)
      (λ _ _ _ _ _ → funext λ _ → code-has-all-cells₂-b _ _)

    -- The data type!
    code : P → Set i
    code = pushout-rec-nondep (Set i) code-a code-b code-glue

    -- Useful lemma
    trans-code-glue : ∀ c₂ co → transport code (glue c₂) co ≡ a⇒b c₂ co
    trans-code-glue c₂ co =
      transport code (glue c₂) co
        ≡⟨ ! $ trans-ap (λ X → X) code (glue c₂) co ⟩
      transport (λ X → X) (ap code (glue c₂)) co
        ≡⟨ ap (λ x → transport (λ X → X) x co)
            $ pushout-β-glue-nondep (Set i) code-a code-b code-glue c₂ ⟩
      transport (λ X → X) (code-glue c₂) co
        ≡⟨ trans-id-eq-to-path (code-glue-eq c₂) co ⟩∎
      a⇒b c₂ co
        ∎

    trans-code-!glue : ∀ c₂ co → transport code (! $ glue c₂) co ≡ b⇒a c₂ co
    trans-code-!glue c₂ co = move!-transp-right code (glue c₂) co (b⇒a c₂ co) $ ! $
      transport code (glue c₂) (b⇒a c₂ co)
        ≡⟨ trans-code-glue c₂ (b⇒a c₂ co) ⟩
      a⇒b c₂ (b⇒a c₂ co)
        ≡⟨ code-glue-bab c₂ co ⟩∎
      co
        ∎

    -- Truncation level
    open import HLevelBis
    abstract
      code-is-set : ∀ {p} → is-set $ code p
      code-is-set {p} = pushout-rec
        (λ p → is-set $ code p)
        (λ _ → code-a-is-set)
        (λ _ → code-b-is-set)
        (λ _ → prop-has-all-paths is-set-is-prop _ _)
        p

