{-# OPTIONS --without-K #-}

open import Base

{-
  The truncated representation for paths from a fixed point
  (a₁ here) in one corner of a pushout (A here).

       g
    C---->B
    |     |
   f|  ~  |right
    v     v
    A---->P
     left

  This is for formalizing the van Kampen theorem.
-}

module Homotopy.VanKampen.CodeHeadMerge {i}
  (C A B : Set i) (f : C → A) (g : C → B) (a₁ : A) where

  open import Homotopy.PushoutDef
  open import Homotopy.Truncation
  open import Spaces.Pi0PathSpace
  P : Set i
  P = pushout (diag A , B , C , f , g)

  open import Homotopy.VanKampen.SplitCode C A B f g a₁ public

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
  code : P → Set i
  code-glue-eq : ∀ c → code-a (f c) ≃ code-b (g c)
  code-glue-aba : ∀ c (co : code-a (f c)) → b⇒a c (a⇒b c co) ≡ co
  code-glue-bab : ∀ c (co : code-b (g c)) → a⇒b c (b⇒a c co) ≡ co
  private
    code-glue : ∀ c → code-a (f c) ≡ code-b (g c)
    code-glue′ : ∀ c
               → (∀ {a₂} co → G-a c {a₂} co)
               × (∀ {b₂} co → G-b c {b₂} co)

  code-glue-aba c co = π₁ (code-glue′ c) co $ refl _
  code-glue-bab c co = π₂ (code-glue′ c) co $ refl _
  code-glue-eq c = a⇒b c , iso-is-eq (a⇒b c) (b⇒a c) (code-glue-bab c) (code-glue-aba c)
  code-glue c = eq-to-path $ code-glue-eq c
  code = pushout-rec-nondep (Set i) code-a code-b code-glue
  code-glue′ c = code-rec
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

  trans-glue : ∀ c₂ co → transport code (glue c₂) co ≡ a⇒b c₂ co
  trans-glue c₂ co =
    transport code (glue c₂) co
      ≡⟨ ! $ trans-ap {P = λ X → X} code (glue c₂) co ⟩
    transport (λ X → X) (ap code (glue c₂)) co
      ≡⟨ ap (λ x → transport (λ X → X) x co)
          $ pushout-β-glue-nondep (Set i) code-a code-b code-glue c₂ ⟩
    transport (λ X → X) (code-glue c₂) co
      ≡⟨ trans-id-eq-to-path (code-glue-eq c₂) co ⟩∎
    a⇒b c₂ co
      ∎

  trans-!glue : ∀ c₂ co → transport code (! $ glue c₂) co ≡ b⇒a c₂ co
  trans-!glue c₂ co = move!-transp-right code (glue c₂) co (b⇒a c₂ co) $ ! $
    transport code (glue c₂) (b⇒a c₂ co)
      ≡⟨ trans-glue c₂ (b⇒a c₂ co) ⟩
    a⇒b c₂ (b⇒a c₂ co)
      ≡⟨ code-glue-bab c₂ co ⟩∎
    co
      ∎

  open import HLevelBis
  abstract
    code-is-set : ∀ {p} → is-set $ code p
    code-is-set {p} = pushout-rec
      (λ p → is-set $ code p)
      (λ _ → code-a-is-set)
      (λ _ → code-b-is-set)
      (λ _ → prop-has-all-paths is-set-is-prop _ _)
      p
