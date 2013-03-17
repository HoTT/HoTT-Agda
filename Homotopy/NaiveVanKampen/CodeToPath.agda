{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Pushout

{-
  This module provides the function code⇒path
  for the homotopy equivalence for (naive)
  van Kampen theorem.
-}

module Homotopy.NaiveVanKampen.CodeToPath {i} (d : pushout-diag i) where

  open pushout-diag d

  open import Homotopy.Truncation
  open import Spaces.Pi0Paths
  open import Homotopy.NaiveVanKampen.Code d

  private
    pg : ∀ c → _≡₀_ {A = P} (left (f c)) (right (g c))
    pg c = proj (glue c)

    p!g : ∀ c → _≡₀_ {A = P} (right (g c)) (left (f c))
    p!g c = proj (! (glue c))

    ap₀l : ∀ {a₁ a₂} → a₁ ≡₀ a₂ → _≡₀_ {A = P} (left a₁) (left a₂)
    ap₀l p = ap₀ left p

    ap₀r : ∀ {b₁ b₂} → b₁ ≡₀ b₂ → _≡₀_ {A = P} (right b₁) (right b₂)
    ap₀r p = ap₀ right p

  module _ {a₁ : A} where
    aa⇒path : ∀ {a₂} → a-code-a a₁ a₂ → _≡₀_ {A = P} (left a₁) (left  a₂)
    ab⇒path : ∀ {b₂} → a-code-b a₁ b₂ → _≡₀_ {A = P} (left a₁) (right b₂)
    private
      ap⇒path-split : (∀ {a₂} → a-code-a a₁ a₂ → _≡₀_ {A = P} (left a₁) (left  a₂))
                    × (∀ {b₂} → a-code-b a₁ b₂ → _≡₀_ {A = P} (left a₁) (right b₂))

    aa⇒path = π₁ ap⇒path-split
    ab⇒path = π₂ ap⇒path-split

    ap⇒path-split = a-code-rec-nondep a₁
      (λ a₂ → left a₁ ≡₀ left  a₂)
      ⦃ λ a₂ → π₀-is-set _ ⦄
      (λ b₂ → left a₁ ≡₀ right b₂)
      ⦃ λ b₂ → π₀-is-set _ ⦄
      (λ p → ap₀l p)
      (λ c pco p → (pco ∘₀ p!g c) ∘₀ ap₀l p)
      (λ c pco p → (pco ∘₀ pg  c) ∘₀ ap₀r p)
      (λ {a₂} c p₁ (p₂ : f c ≡₀ a₂) →
        (((ap₀l p₁ ∘₀ pg c) ∘₀ refl₀ _) ∘₀ p!g c) ∘₀ ap₀l p₂
          ≡⟨ ap (λ x → (x ∘₀ p!g c) ∘₀ ap₀l p₂)
                $ refl₀-right-unit $ ap₀l p₁ ∘₀ pg c ⟩
        ((ap₀l p₁ ∘₀ pg c) ∘₀ p!g c) ∘₀ ap₀l p₂
          ≡⟨ ap (λ x → x ∘₀ ap₀l p₂) $ concat₀-assoc (ap₀l p₁) (pg c) (p!g c) ⟩
        (ap₀l p₁ ∘₀ (pg c ∘₀ p!g c)) ∘₀ ap₀l p₂
          ≡⟨ ap (λ x → (ap₀l p₁ ∘₀ proj x) ∘₀ ap₀l p₂)
                $ opposite-right-inverse $ glue c ⟩
        (ap₀l p₁ ∘₀ refl₀ _) ∘₀ ap₀l p₂
          ≡⟨ ap (λ x → x ∘₀ ap₀l p₂) $ refl₀-right-unit $ ap₀l p₁ ⟩
        ap₀l p₁ ∘₀ ap₀l p₂
          ≡⟨ concat₀-ap₀ left p₁ p₂ ⟩∎
        ap₀l (p₁ ∘₀ p₂)
          ∎)
      (λ c₁ pco c₂ p₁ p₂ →
        (((((pco ∘₀ p!g c₁) ∘₀ ap₀l p₁) ∘₀ pg c₂) ∘₀ refl₀ _) ∘₀ p!g c₂) ∘₀ ap₀l p₂
          ≡⟨ ap (λ x → (x ∘₀ p!g c₂) ∘₀ ap₀l p₂)
                $ refl₀-right-unit $ ((pco ∘₀ p!g c₁) ∘₀ ap₀l p₁) ∘₀ pg c₂ ⟩
        ((((pco ∘₀ p!g c₁) ∘₀ ap₀l p₁) ∘₀ pg c₂) ∘₀ p!g c₂) ∘₀ ap₀l p₂
          ≡⟨ ap (λ x → x ∘₀ ap₀l p₂)
                $ concat₀-assoc ((pco ∘₀ p!g c₁) ∘₀ ap₀l p₁) (pg c₂) (p!g c₂) ⟩
        (((pco ∘₀ p!g c₁) ∘₀ ap₀l p₁) ∘₀ (pg c₂ ∘₀ p!g c₂)) ∘₀ ap₀l p₂
          ≡⟨ ap (λ x → (((pco ∘₀ p!g c₁) ∘₀ ap₀l p₁) ∘₀ proj x) ∘₀ ap₀l p₂)
                $ opposite-right-inverse $ glue c₂ ⟩
        (((pco ∘₀ p!g c₁) ∘₀ ap₀l p₁) ∘₀ refl₀ _) ∘₀ ap₀l p₂
          ≡⟨ ap (λ x → x ∘₀ ap₀l p₂) $ refl₀-right-unit $ (pco ∘₀ p!g c₁) ∘₀ ap₀l p₁ ⟩
        ((pco ∘₀ p!g c₁) ∘₀ ap₀l p₁) ∘₀ ap₀l p₂
          ≡⟨ concat₀-assoc (pco ∘₀ p!g c₁) (ap₀l p₁) (ap₀l p₂) ⟩
        (pco ∘₀ p!g c₁) ∘₀ (ap₀l p₁ ∘₀ ap₀l p₂)
          ≡⟨ ap (λ x → (pco ∘₀ p!g c₁) ∘₀ x) $ concat₀-ap₀ left p₁ p₂ ⟩∎
        (pco ∘₀ p!g c₁) ∘₀ ap₀l (p₁ ∘₀ p₂)
          ∎)
      (λ c₁ pco c₂ p₁ p₂ →
        (((((pco ∘₀ pg c₁) ∘₀ ap₀r p₁) ∘₀ p!g c₂) ∘₀ refl₀ _) ∘₀ pg c₂) ∘₀ ap₀r p₂
          ≡⟨ ap (λ x → (x ∘₀ pg c₂) ∘₀ ap₀r p₂)
                $ refl₀-right-unit $ ((pco ∘₀ pg c₁) ∘₀ ap₀r p₁) ∘₀ p!g c₂ ⟩
        ((((pco ∘₀ pg c₁) ∘₀ ap₀r p₁) ∘₀ p!g c₂) ∘₀ pg c₂) ∘₀ ap₀r p₂
          ≡⟨ ap (λ x → x ∘₀ ap₀r p₂)
                $ concat₀-assoc ((pco ∘₀ pg c₁) ∘₀ ap₀r p₁) (p!g c₂) (pg c₂) ⟩
        (((pco ∘₀ pg c₁) ∘₀ ap₀r p₁) ∘₀ (p!g c₂ ∘₀ pg c₂)) ∘₀ ap₀r p₂
          ≡⟨ ap (λ x → (((pco ∘₀ pg c₁) ∘₀ ap₀r p₁) ∘₀ proj x) ∘₀ ap₀r p₂)
                $ opposite-left-inverse $ glue c₂ ⟩
        (((pco ∘₀ pg c₁) ∘₀ ap₀r p₁) ∘₀ refl₀ _) ∘₀ ap₀r p₂
          ≡⟨ ap (λ x → x ∘₀ ap₀r p₂) $ refl₀-right-unit $ (pco ∘₀ pg c₁) ∘₀ ap₀r p₁ ⟩
        ((pco ∘₀ pg c₁) ∘₀ ap₀r p₁) ∘₀ ap₀r p₂
          ≡⟨ concat₀-assoc (pco ∘₀ pg c₁) (ap₀r p₁) (ap₀r p₂) ⟩
        (pco ∘₀ pg c₁) ∘₀ (ap₀r p₁ ∘₀ ap₀r p₂)
          ≡⟨ ap (λ x → (pco ∘₀ pg c₁) ∘₀ x) $ concat₀-ap₀ right p₁ p₂ ⟩∎
        (pco ∘₀ pg c₁) ∘₀ ap₀r (p₁ ∘₀ p₂)
          ∎)

    ap⇒path : ∀ {p₂ : P} → a-code a₁ p₂ → left a₁ ≡₀ p₂
    ap⇒path {p₂} = pushout-rec
      (λ p → a-code a₁ p → left a₁ ≡₀ p)
      (λ a → aa⇒path {a})
      (λ b → ab⇒path {b})
      (λ c → funext λ co →
          transport (λ p → a-code a₁ p → left a₁ ≡₀ p) (glue c) aa⇒path co
              ≡⟨ trans-→ (a-code a₁) (λ x → left a₁ ≡₀ x) (glue c) aa⇒path co ⟩
          transport (λ p → left a₁ ≡₀ p) (glue c) (aa⇒path $ transport (a-code a₁) (! (glue c)) co)
              ≡⟨ ap (transport (λ p → left a₁ ≡₀ p) (glue c) ◯ aa⇒path) $ trans-a-code-!glue c co ⟩
          transport (λ p → left a₁ ≡₀ p) (glue c) (aa⇒path $ ab⇒aa c co)
              ≡⟨ trans-cst≡₀id (glue c) (aa⇒path $ ab⇒aa c co) ⟩
          (aa⇒path $ ab⇒aa c co) ∘₀ pg c
              ≡⟨ refl _ ⟩
          ((ab⇒path co ∘₀ p!g c) ∘₀ refl₀ _) ∘₀ pg c
              ≡⟨ ap (λ x → x ∘₀ pg c) $ refl₀-right-unit $ ab⇒path co ∘₀ p!g c ⟩
          (ab⇒path co ∘₀ p!g c) ∘₀ pg c
              ≡⟨ concat₀-assoc (ab⇒path co) (p!g c) (pg c) ⟩
          ab⇒path co ∘₀ (p!g c ∘₀ pg c)
              ≡⟨ ap (λ x → ab⇒path co ∘₀ proj x) $ opposite-left-inverse $ glue c ⟩
          ab⇒path co ∘₀ refl₀ _
              ≡⟨ refl₀-right-unit $ ab⇒path co ⟩∎
          ab⇒path co
              ∎)
      p₂

  -- FIXME
  -- There is tension between reducing duplicate code and
  -- maintaining definitional equality. I could not make
  -- the neccessary type conversion definitional, so
  -- I just copied and pasted the previous module.
  module _ {b₁ : B} where
    ba⇒path : ∀ {a₂} → b-code-a b₁ a₂ → _≡₀_ {A = P} (right b₁) (left  a₂)
    bb⇒path : ∀ {b₂} → b-code-b b₁ b₂ → _≡₀_ {A = P} (right b₁) (right b₂)
    private
      bp⇒path-split : (∀ {b₂} → b-code-b b₁ b₂ → _≡₀_ {A = P} (right b₁) (right b₂))
                    × (∀ {a₂} → b-code-a b₁ a₂ → _≡₀_ {A = P} (right b₁) (left  a₂))

    ba⇒path = π₂ bp⇒path-split
    bb⇒path = π₁ bp⇒path-split

    bp⇒path-split = b-code-rec-nondep b₁
      (λ b₂ → right b₁ ≡₀ right b₂)
      ⦃ λ b₂ → π₀-is-set _ ⦄
      (λ a₂ → right b₁ ≡₀ left  a₂)
      ⦃ λ a₂ → π₀-is-set _ ⦄
      (λ p → ap₀r p)
      (λ c pco p → (pco ∘₀ pg  c) ∘₀ ap₀r p)
      (λ c pco p → (pco ∘₀ p!g c) ∘₀ ap₀l p)
      (λ {b₂} c p₁ (p₂ : g c ≡₀ b₂) →
        (((ap₀r p₁ ∘₀ p!g c) ∘₀ refl₀ _) ∘₀ pg c) ∘₀ ap₀r p₂
          ≡⟨ ap (λ x → (x ∘₀ pg c) ∘₀ ap₀r p₂)
                $ refl₀-right-unit $ ap₀r p₁ ∘₀ p!g c ⟩
        ((ap₀r p₁ ∘₀ p!g c) ∘₀ pg c) ∘₀ ap₀r p₂
          ≡⟨ ap (λ x → x ∘₀ ap₀r p₂) $ concat₀-assoc (ap₀r p₁) (p!g c) (pg c) ⟩
        (ap₀r p₁ ∘₀ (p!g c ∘₀ pg c)) ∘₀ ap₀r p₂
          ≡⟨ ap (λ x → (ap₀r p₁ ∘₀ proj x) ∘₀ ap₀r p₂)
                $ opposite-left-inverse $ glue c ⟩
        (ap₀r p₁ ∘₀ refl₀ _) ∘₀ ap₀r p₂
          ≡⟨ ap (λ x → x ∘₀ ap₀r p₂) $ refl₀-right-unit $ ap₀r p₁ ⟩
        ap₀r p₁ ∘₀ ap₀r p₂
          ≡⟨ concat₀-ap₀ right p₁ p₂ ⟩∎
        ap₀r (p₁ ∘₀ p₂)
          ∎)
      (λ c₁ pco c₂ p₁ p₂ →
        (((((pco ∘₀ pg c₁) ∘₀ ap₀r p₁) ∘₀ p!g c₂) ∘₀ refl₀ _) ∘₀ pg c₂) ∘₀ ap₀r p₂
          ≡⟨ ap (λ x → (x ∘₀ pg c₂) ∘₀ ap₀r p₂)
                $ refl₀-right-unit $ ((pco ∘₀ pg c₁) ∘₀ ap₀r p₁) ∘₀ p!g c₂ ⟩
        ((((pco ∘₀ pg c₁) ∘₀ ap₀r p₁) ∘₀ p!g c₂) ∘₀ pg c₂) ∘₀ ap₀r p₂
          ≡⟨ ap (λ x → x ∘₀ ap₀r p₂)
                $ concat₀-assoc ((pco ∘₀ pg c₁) ∘₀ ap₀r p₁) (p!g c₂) (pg c₂) ⟩
        (((pco ∘₀ pg c₁) ∘₀ ap₀r p₁) ∘₀ (p!g c₂ ∘₀ pg c₂)) ∘₀ ap₀r p₂
          ≡⟨ ap (λ x → (((pco ∘₀ pg c₁) ∘₀ ap₀r p₁) ∘₀ proj x) ∘₀ ap₀r p₂)
                $ opposite-left-inverse $ glue c₂ ⟩
        (((pco ∘₀ pg c₁) ∘₀ ap₀r p₁) ∘₀ refl₀ _) ∘₀ ap₀r p₂
          ≡⟨ ap (λ x → x ∘₀ ap₀r p₂) $ refl₀-right-unit $ (pco ∘₀ pg c₁) ∘₀ ap₀r p₁ ⟩
        ((pco ∘₀ pg c₁) ∘₀ ap₀r p₁) ∘₀ ap₀r p₂
          ≡⟨ concat₀-assoc (pco ∘₀ pg c₁) (ap₀r p₁) (ap₀r p₂) ⟩
        (pco ∘₀ pg c₁) ∘₀ (ap₀r p₁ ∘₀ ap₀r p₂)
          ≡⟨ ap (λ x → (pco ∘₀ pg c₁) ∘₀ x) $ concat₀-ap₀ right p₁ p₂ ⟩∎
        (pco ∘₀ pg c₁) ∘₀ ap₀r (p₁ ∘₀ p₂)
          ∎)
      (λ c₁ pco c₂ p₁ p₂ →
        (((((pco ∘₀ p!g c₁) ∘₀ ap₀l p₁) ∘₀ pg c₂) ∘₀ refl₀ _) ∘₀ p!g c₂) ∘₀ ap₀l p₂
          ≡⟨ ap (λ x → (x ∘₀ p!g c₂) ∘₀ ap₀l p₂)
                $ refl₀-right-unit $ ((pco ∘₀ p!g c₁) ∘₀ ap₀l p₁) ∘₀ pg c₂ ⟩
        ((((pco ∘₀ p!g c₁) ∘₀ ap₀l p₁) ∘₀ pg c₂) ∘₀ p!g c₂) ∘₀ ap₀l p₂
          ≡⟨ ap (λ x → x ∘₀ ap₀l p₂)
                $ concat₀-assoc ((pco ∘₀ p!g c₁) ∘₀ ap₀l p₁) (pg c₂) (p!g c₂) ⟩
        (((pco ∘₀ p!g c₁) ∘₀ ap₀l p₁) ∘₀ (pg c₂ ∘₀ p!g c₂)) ∘₀ ap₀l p₂
          ≡⟨ ap (λ x → (((pco ∘₀ p!g c₁) ∘₀ ap₀l p₁) ∘₀ proj x) ∘₀ ap₀l p₂)
                $ opposite-right-inverse $ glue c₂ ⟩
        (((pco ∘₀ p!g c₁) ∘₀ ap₀l p₁) ∘₀ refl₀ _) ∘₀ ap₀l p₂
          ≡⟨ ap (λ x → x ∘₀ ap₀l p₂) $ refl₀-right-unit $ (pco ∘₀ p!g c₁) ∘₀ ap₀l p₁ ⟩
        ((pco ∘₀ p!g c₁) ∘₀ ap₀l p₁) ∘₀ ap₀l p₂
          ≡⟨ concat₀-assoc (pco ∘₀ p!g c₁) (ap₀l p₁) (ap₀l p₂) ⟩
        (pco ∘₀ p!g c₁) ∘₀ (ap₀l p₁ ∘₀ ap₀l p₂)
          ≡⟨ ap (λ x → (pco ∘₀ p!g c₁) ∘₀ x) $ concat₀-ap₀ left p₁ p₂ ⟩∎
        (pco ∘₀ p!g c₁) ∘₀ ap₀l (p₁ ∘₀ p₂)
          ∎)

    bp⇒path : ∀ {p₂ : P} → b-code b₁ p₂ → right b₁ ≡₀ p₂
    bp⇒path {p₂} = pushout-rec
      (λ p → b-code b₁ p → right b₁ ≡₀ p)
      (λ a → ba⇒path {a})
      (λ b → bb⇒path {b})
      (λ c → funext λ co →
          transport (λ p → b-code b₁ p → right b₁ ≡₀ p) (glue c) ba⇒path co
              ≡⟨ trans-→ (b-code b₁) (λ x → right b₁ ≡₀ x) (glue c) ba⇒path co ⟩
          transport (λ p → right b₁ ≡₀ p) (glue c) (ba⇒path $ transport (b-code b₁) (! (glue c)) co)
              ≡⟨ ap (transport (λ p → right b₁ ≡₀ p) (glue c) ◯ ba⇒path)
                    $ trans-b-code-!glue {b₁} c co ⟩
          transport (λ p → right b₁ ≡₀ p) (glue c) (ba⇒path $ bb⇒ba c co)
              ≡⟨ trans-cst≡₀id (glue c) (ba⇒path $ bb⇒ba c co) ⟩
          (ba⇒path $ bb⇒ba c co) ∘₀ pg c
              ≡⟨ refl _ ⟩
          ((bb⇒path co ∘₀ p!g c) ∘₀ refl₀ _) ∘₀ pg c
              ≡⟨ ap (λ x → x ∘₀ pg c) $ refl₀-right-unit $ bb⇒path co ∘₀ p!g c ⟩
          (bb⇒path co ∘₀ p!g c) ∘₀ pg c
              ≡⟨ concat₀-assoc (bb⇒path co) (p!g c) (pg c) ⟩
          bb⇒path co ∘₀ (p!g c ∘₀ pg c)
              ≡⟨ ap (λ x → bb⇒path co ∘₀ proj x) $ opposite-left-inverse $ glue c ⟩
          bb⇒path co ∘₀ refl₀ _
              ≡⟨ refl₀-right-unit $ bb⇒path co ⟩∎
          bb⇒path co
              ∎)
      p₂

  module _ where

    private
      Lbaaa : ∀ c {a₂} → b-code-a (g c) a₂ → Set i
      Lbaaa = λ c co → aa⇒path {f c} (ba⇒aa c co) ≡ pg c ∘₀ ba⇒path co
      Lbbab : ∀ c {b₂} → b-code-b (g c) b₂ → Set i
      Lbbab = λ c co → ab⇒path {f c} (bb⇒ab c co) ≡ pg c ∘₀ bb⇒path co
    private
      ba⇒aa⇒path : ∀ c {a₂} (co : b-code-a (g c) a₂) → Lbaaa c co
      bb⇒ab⇒path : ∀ c {b₂} (co : b-code-b (g c) b₂) → Lbbab c co
      bp⇒ap⇒path-split : ∀ c
        → (∀ {a₂} co → Lbbab c {a₂} co)
        × (∀ {b₂} co → Lbaaa c {b₂} co)
      bb⇒ab⇒path c = π₁ $ bp⇒ap⇒path-split c
      ba⇒aa⇒path c = π₂ $ bp⇒ap⇒path-split c
      bp⇒ap⇒path-split c = b-code-rec (g c)
        (λ co → ab⇒path {f c} (bb⇒ab c co) ≡ pg c ∘₀ bb⇒path co)
        ⦃ λ _ → ≡-is-set $ π₀-is-set _ ⦄
        (λ co → aa⇒path {f c} (ba⇒aa c co) ≡ pg c ∘₀ ba⇒path co)
        ⦃ λ _ → ≡-is-set $ π₀-is-set _ ⦄
        (λ p →
          ab⇒path (bb⇒ab c (⟧b p))
            ≡⟨ refl _ ⟩
          ab⇒path (⟧a refl₀ _ aa⟦ c ⟧b p)
            ≡⟨ refl _ ⟩
          (refl₀ _ ∘₀ pg c) ∘₀ ap₀r p
            ≡⟨ ap (λ x → x ∘₀ ap₀r p) $ refl₀-left-unit $ pg c ⟩
          pg c ∘₀ ap₀r p
            ≡⟨ refl _ ⟩∎
          pg c ∘₀ bb⇒path (⟧b p)
            ∎)
        (λ c₁ {co} eq p₁ →
          (aa⇒path (ba⇒aa c co) ∘₀ pg c₁) ∘₀ ap₀r p₁
            ≡⟨ ap (λ x → (x ∘₀ pg c₁) ∘₀ ap₀r p₁) eq ⟩
          ((pg c ∘₀ ba⇒path co) ∘₀ pg c₁) ∘₀ ap₀r p₁
            ≡⟨ ap (λ x → x ∘₀ ap₀r p₁)
                  $ concat₀-assoc (pg c) (ba⇒path co) (pg c₁) ⟩
          (pg c ∘₀ (ba⇒path co ∘₀ pg c₁)) ∘₀ ap₀r p₁
            ≡⟨ concat₀-assoc (pg c) (ba⇒path co ∘₀ pg c₁) (ap₀r p₁) ⟩∎
          pg c ∘₀ ((ba⇒path co ∘₀ pg c₁) ∘₀ ap₀r p₁)
            ∎)
        (λ c₁ {co} eq p₁ →
          (ab⇒path (bb⇒ab c co) ∘₀ p!g c₁) ∘₀ ap₀l p₁
            ≡⟨ ap (λ x → (x ∘₀ p!g c₁) ∘₀ ap₀l p₁) eq ⟩
          ((pg c ∘₀ bb⇒path co) ∘₀ p!g c₁) ∘₀ ap₀l p₁
            ≡⟨ ap (λ x → x ∘₀ ap₀l p₁)
                  $ concat₀-assoc (pg c) (bb⇒path co) (p!g c₁) ⟩
          (pg c ∘₀ (bb⇒path co ∘₀ p!g c₁)) ∘₀ ap₀l p₁
            ≡⟨ concat₀-assoc (pg c) (bb⇒path co ∘₀ p!g c₁) (ap₀l p₁) ⟩∎
          pg c ∘₀ ((bb⇒path co ∘₀ p!g c₁) ∘₀ ap₀l p₁)
            ∎)
        (λ _ _ _ → prop-has-all-paths (π₀-is-set _ _ _) _ _)
        (λ _ _ _ _ _ → prop-has-all-paths (π₀-is-set _ _ _) _ _)
        (λ _ _ _ _ _ → prop-has-all-paths (π₀-is-set _ _ _) _ _)

      bp⇒ap⇒path : ∀ c {p₂} (co : b-code (g c) p₂)
        → ap⇒path {f c} {p₂} (bp⇒ap c {p₂} co)
        ≡ pg c ∘₀ bp⇒path {g c} {p₂} co
      bp⇒ap⇒path c {p₂} = pushout-rec
        (λ x → ∀ (co : b-code (g c) x)
               → ap⇒path {f c} {x} (bp⇒ap c {x} co)
               ≡ pg c ∘₀ bp⇒path {g c} {x} co)
        (λ a₂ → ba⇒aa⇒path c {a₂})
        (λ b₂ → bb⇒ab⇒path c {b₂})
        (λ _ → funext λ _ → prop-has-all-paths (π₀-is-set _ _ _) _ _)
        p₂

    code⇒path : ∀ {p₁ p₂} → code p₁ p₂ → p₁ ≡₀ p₂
    code⇒path {p₁} {p₂} = pushout-rec
      (λ p₁ → code p₁ p₂ → p₁ ≡₀ p₂)
      (λ a → ap⇒path {a} {p₂})
      (λ b → bp⇒path {b} {p₂})
      (λ c → funext λ (co : code (right $ g c) p₂) →
        transport (λ x → code x p₂ → x ≡₀ p₂) (glue c) (ap⇒path {f c} {p₂}) co
            ≡⟨ trans-→ (λ x → code x p₂) (λ x → x ≡₀ p₂) (glue c) (ap⇒path {f c} {p₂}) co ⟩
        transport (λ x → x ≡₀ p₂) (glue c) (ap⇒path {f c} {p₂}
          $ transport (λ x → code x p₂) (! (glue c)) co)
            ≡⟨ ap (transport (λ x → x ≡₀ p₂) (glue c) ◯ ap⇒path {f c} {p₂})
                  $ trans-!glue-code c {p₂} co ⟩
        transport (λ x → x ≡₀ p₂) (glue c) (ap⇒path {f c} {p₂} $ bp⇒ap c {p₂} co)
            ≡⟨ ap (transport (λ x → x ≡₀ p₂) (glue c)) $ bp⇒ap⇒path c {p₂} co ⟩
        transport (λ x → x ≡₀ p₂) (glue c) (pg c ∘₀ bp⇒path {g c} {p₂} co)
            ≡⟨ trans-id≡₀cst (glue c) (pg c ∘₀ bp⇒path {g c} {p₂} co) ⟩
        p!g c ∘₀ (pg c ∘₀ bp⇒path {g c} {p₂} co)
            ≡⟨ ! $ concat₀-assoc (p!g c) (pg c) (bp⇒path {g c} {p₂} co) ⟩
        (p!g c ∘₀ pg c) ∘₀ bp⇒path {g c} {p₂} co
            ≡⟨ ap (λ x → proj x ∘₀ bp⇒path {g c} {p₂} co) $ opposite-left-inverse (glue c) ⟩
        refl₀ (right (g c)) ∘₀ bp⇒path {g c} {p₂} co
            ≡⟨ refl₀-left-unit (bp⇒path {g c} {p₂} co) ⟩∎
        bp⇒path {g c} {p₂} co
            ∎)
      p₁
