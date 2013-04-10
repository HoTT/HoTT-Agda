{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Pushout
open import Homotopy.VanKampen.Guide

{-
  This module provides the function code⇒path
  for the homotopy equivalence for
  van Kampen theorem.
-}

module Homotopy.VanKampen.CodeToPath {i} (d : pushout-diag i)
  (l : legend i (pushout-diag.C d)) where

  open pushout-diag d
  open legend l

  open import Homotopy.Truncation
  open import Homotopy.PathTruncation
  open import Homotopy.VanKampen.Code d l

  private
    pgl : ∀ n → _≡₀_ {A = P} (left (f $ loc n)) (right (g $ loc n))
    pgl n = proj (glue $ loc n)

    p!gl : ∀ n → _≡₀_ {A = P} (right (g $ loc n)) (left (f $ loc n))
    p!gl n = proj (! (glue $ loc n))

    ap₀l : ∀ {a₁ a₂} → a₁ ≡₀ a₂ → _≡₀_ {A = P} (left a₁) (left a₂)
    ap₀l p = ap₀ left p

    ap₀r : ∀ {b₁ b₂} → b₁ ≡₀ b₂ → _≡₀_ {A = P} (right b₁) (right b₂)
    ap₀r p = ap₀ right p

  module _ {a₁ : A} where
    private
      ap⇒path-split : (∀ {a₂} → a-code-a a₁ a₂ → _≡₀_ {A = P} (left a₁) (left  a₂))
                    × (∀ {b₂} → a-code-b a₁ b₂ → _≡₀_ {A = P} (left a₁) (right b₂))
      ap⇒path-split = a-code-rec-nondep a₁
        (λ a₂ → left a₁ ≡₀ left  a₂)
        ⦃ λ a₂ → π₀-is-set _ ⦄
        (λ b₂ → left a₁ ≡₀ right b₂)
        ⦃ λ b₂ → π₀-is-set _ ⦄
        (λ p → ap₀l p)
        (λ n pco p → (pco ∘₀ p!gl n) ∘₀ ap₀l p)
        (λ n pco p → (pco ∘₀ pgl  n) ∘₀ ap₀r p)
        (λ n {co} pco →
          (((pco ∘₀ pgl n) ∘₀ refl₀) ∘₀ p!gl n) ∘₀ refl₀
            ≡⟨ refl₀-right-unit _ ⟩
          ((pco ∘₀ pgl n) ∘₀ refl₀) ∘₀ p!gl n
            ≡⟨ ap (λ x → x ∘₀ p!gl n)
                  $ refl₀-right-unit $ pco ∘₀ pgl n ⟩
          (pco ∘₀ pgl n) ∘₀ p!gl n
            ≡⟨ concat₀-assoc pco (pgl n) (p!gl n) ⟩
          pco ∘₀ (pgl n ∘₀ p!gl n)
            ≡⟨ ap (λ x → pco ∘₀ proj x)
                  $ opposite-right-inverse $ glue $ loc n ⟩
          pco ∘₀ refl₀
            ≡⟨ refl₀-right-unit pco ⟩∎
          pco
            ∎)
        (λ n {co} pco →
          (((pco ∘₀ p!gl n) ∘₀ refl₀) ∘₀ pgl n) ∘₀ refl₀
            ≡⟨ refl₀-right-unit _ ⟩
          ((pco ∘₀ p!gl n) ∘₀ refl₀) ∘₀ pgl n
            ≡⟨ ap (λ x → x ∘₀ pgl n)
                  $ refl₀-right-unit $ pco ∘₀ p!gl n ⟩
          (pco ∘₀ p!gl n) ∘₀ pgl n
            ≡⟨ concat₀-assoc pco (p!gl n) (pgl n) ⟩
          pco ∘₀ (p!gl n ∘₀ pgl n)
            ≡⟨ ap (λ x → pco ∘₀ proj x)
                  $ opposite-left-inverse $ glue $ loc n ⟩
          pco ∘₀ refl₀
            ≡⟨ refl₀-right-unit pco ⟩∎
          pco
            ∎)
        (λ n₁ {co} pco n₂ r →
          (((pco ∘₀ pgl n₁) ∘₀ ap₀r (ap₀ g r)) ∘₀ p!gl n₂) ∘₀ refl₀
            ≡⟨ refl₀-right-unit _ ⟩
          ((pco ∘₀ pgl n₁) ∘₀ ap₀r (ap₀ g r)) ∘₀ p!gl n₂
            ≡⟨ concat₀-assoc (pco ∘₀ pgl n₁) (ap₀r (ap₀ g r)) (p!gl n₂) ⟩
          (pco ∘₀ pgl n₁) ∘₀ (ap₀r (ap₀ g r) ∘₀ p!gl n₂)
            ≡⟨ ap (λ x → (pco ∘₀ pgl n₁) ∘₀ (x ∘₀ p!gl n₂)) $ ! $ ap₀-compose right g r ⟩
          (pco ∘₀ pgl n₁) ∘₀ (ap₀ (right ◯ g) r ∘₀ p!gl n₂)
            ≡⟨ ap (λ x → (pco ∘₀ pgl n₁) ∘₀ x)
                  $ homotopy₀-naturality (right ◯ g) (left ◯ f) (proj ◯ (! ◯ glue)) r ⟩
          (pco ∘₀ pgl n₁) ∘₀ (p!gl n₁ ∘₀ ap₀ (left ◯ f) r)
            ≡⟨ ! $ concat₀-assoc (pco ∘₀ pgl n₁) (p!gl n₁) (ap₀ (left ◯ f) r) ⟩
          ((pco ∘₀ pgl n₁) ∘₀ p!gl n₁) ∘₀ ap₀ (left ◯ f) r
            ≡⟨ ap (λ x → ((pco ∘₀ pgl n₁) ∘₀ p!gl n₁) ∘₀ x) $ ap₀-compose left f r ⟩
          ((pco ∘₀ pgl n₁) ∘₀ p!gl n₁) ∘₀ ap₀l (ap₀ f r)
            ≡⟨ ap (λ x → (x ∘₀ p!gl n₁) ∘₀ ap₀l (ap₀ f r))
                  $ ! $ refl₀-right-unit $ pco ∘₀ pgl n₁ ⟩∎
          (((pco ∘₀ pgl n₁) ∘₀ refl₀) ∘₀ p!gl n₁) ∘₀ ap₀l (ap₀ f r)
            ∎)

    aa⇒path : ∀ {a₂} → a-code-a a₁ a₂ → _≡₀_ {A = P} (left a₁) (left  a₂)
    aa⇒path = π₁ ap⇒path-split
    ab⇒path : ∀ {b₂} → a-code-b a₁ b₂ → _≡₀_ {A = P} (left a₁) (right b₂)
    ab⇒path = π₂ ap⇒path-split

    ap⇒path : ∀ {p₂ : P} → a-code a₁ p₂ → left a₁ ≡₀ p₂
    ap⇒path {p₂} = pushout-rec
      (λ p → a-code a₁ p → left a₁ ≡₀ p)
      (λ a → aa⇒path {a})
      (λ b → ab⇒path {b})
      (loc-fiber-rec l
        (λ c → transport (λ p → a-code a₁ p → left a₁ ≡₀ p) (glue c) aa⇒path
             ≡ ab⇒path)
        ⦃ λ c → →-is-set (π₀-is-set (left a₁ ≡ right (g c))) _ _ ⦄
        (λ n → funext λ co →
            transport (λ p → a-code a₁ p → left a₁ ≡₀ p) (glue $ loc n) aa⇒path co
                ≡⟨ trans-→ (a-code a₁) (λ x → left a₁ ≡₀ x) (glue $ loc n) aa⇒path co ⟩
            transport (λ p → left a₁ ≡₀ p) (glue $ loc n) (aa⇒path $ transport (a-code a₁) (! (glue $ loc n)) co)
                ≡⟨ ap (transport (λ p → left a₁ ≡₀ p) (glue $ loc n) ◯ aa⇒path) $ trans-a-code-!glue-loc n co ⟩
            transport (λ p → left a₁ ≡₀ p) (glue $ loc n) (aa⇒path $ ab⇒aa n co)
                ≡⟨ trans-cst≡₀id (glue $ loc n) (aa⇒path $ ab⇒aa n co) ⟩
            (aa⇒path $ ab⇒aa n co) ∘₀ pgl n
                ≡⟨ refl ⟩
            ((ab⇒path co ∘₀ p!gl n) ∘₀ refl₀) ∘₀ pgl n
                ≡⟨ ap (λ x → x ∘₀ pgl n) $ refl₀-right-unit $ ab⇒path co ∘₀ p!gl n ⟩
            (ab⇒path co ∘₀ p!gl n) ∘₀ pgl n
                ≡⟨ concat₀-assoc (ab⇒path co) (p!gl n) (pgl n) ⟩
            ab⇒path co ∘₀ (p!gl n ∘₀ pgl n)
                ≡⟨ ap (λ x → ab⇒path co ∘₀ proj x) $ opposite-left-inverse $ glue $ loc n ⟩
            ab⇒path co ∘₀ refl₀
                ≡⟨ refl₀-right-unit $ ab⇒path co ⟩∎
            ab⇒path co
                ∎))
      p₂

  -- FIXME
  -- There is tension between reducing duplicate code and
  -- maintaining definitional equality. I could not make
  -- the neccessary type conversion definitional, so
  -- I just copied and pasted the previous module.
  module _ {b₁ : B} where
    private
      bp⇒path-split : (∀ {b₂} → b-code-b b₁ b₂ → _≡₀_ {A = P} (right b₁) (right  b₂))
                    × (∀ {a₂} → b-code-a b₁ a₂ → _≡₀_ {A = P} (right b₁) (left a₂))
      bp⇒path-split = b-code-rec-nondep b₁
        (λ b₂ → right b₁ ≡₀ right  b₂)
        ⦃ λ b₂ → π₀-is-set _ ⦄
        (λ a₂ → right b₁ ≡₀ left a₂)
        ⦃ λ a₂ → π₀-is-set _ ⦄
        (λ p → ap₀r p)
        (λ n pco p → (pco ∘₀ pgl  n) ∘₀ ap₀r p)
        (λ n pco p → (pco ∘₀ p!gl n) ∘₀ ap₀l p)
        (λ n {co} pco →
          (((pco ∘₀ p!gl n) ∘₀ refl₀) ∘₀ pgl n) ∘₀ refl₀
            ≡⟨ refl₀-right-unit _ ⟩
          ((pco ∘₀ p!gl n) ∘₀ refl₀) ∘₀ pgl n
            ≡⟨ ap (λ x → x ∘₀ pgl n)
                  $ refl₀-right-unit $ pco ∘₀ p!gl n ⟩
          (pco ∘₀ p!gl n) ∘₀ pgl n
            ≡⟨ concat₀-assoc pco (p!gl n) (pgl n) ⟩
          pco ∘₀ (p!gl n ∘₀ pgl n)
            ≡⟨ ap (λ x → pco ∘₀ proj x)
                  $ opposite-left-inverse $ glue $ loc n ⟩
          pco ∘₀ refl₀
            ≡⟨ refl₀-right-unit pco ⟩∎
          pco
            ∎)
        (λ n {co} pco →
          (((pco ∘₀ pgl n) ∘₀ refl₀) ∘₀ p!gl n) ∘₀ refl₀
            ≡⟨ refl₀-right-unit _ ⟩
          ((pco ∘₀ pgl n) ∘₀ refl₀) ∘₀ p!gl n
            ≡⟨ ap (λ x → x ∘₀ p!gl n)
                  $ refl₀-right-unit $ pco ∘₀ pgl n ⟩
          (pco ∘₀ pgl n) ∘₀ p!gl n
            ≡⟨ concat₀-assoc pco (pgl n) (p!gl n) ⟩
          pco ∘₀ (pgl n ∘₀ p!gl n)
            ≡⟨ ap (λ x → pco ∘₀ proj x)
                  $ opposite-right-inverse $ glue $ loc n ⟩
          pco ∘₀ refl₀
            ≡⟨ refl₀-right-unit pco ⟩∎
          pco
            ∎)
        (λ n₁ {co} pco n₂ r →
          (((pco ∘₀ p!gl n₁) ∘₀ ap₀l (ap₀ f r)) ∘₀ pgl n₂) ∘₀ refl₀
            ≡⟨ refl₀-right-unit _ ⟩
          ((pco ∘₀ p!gl n₁) ∘₀ ap₀l (ap₀ f r)) ∘₀ pgl n₂
            ≡⟨ concat₀-assoc (pco ∘₀ p!gl n₁) (ap₀l (ap₀ f r)) (pgl n₂) ⟩
          (pco ∘₀ p!gl n₁) ∘₀ (ap₀l (ap₀ f r) ∘₀ pgl n₂)
            ≡⟨ ap (λ x → (pco ∘₀ p!gl n₁) ∘₀ (x ∘₀ pgl n₂)) $ ! $ ap₀-compose left f r ⟩
          (pco ∘₀ p!gl n₁) ∘₀ (ap₀ (left ◯ f) r ∘₀ pgl n₂)
            ≡⟨ ap (λ x → (pco ∘₀ p!gl n₁) ∘₀ x)
                  $ homotopy₀-naturality (left ◯ f) (right ◯ g) (proj ◯  glue) r ⟩
          (pco ∘₀ p!gl n₁) ∘₀ (pgl n₁ ∘₀ ap₀ (right ◯ g) r)
            ≡⟨ ! $ concat₀-assoc (pco ∘₀ p!gl n₁) (pgl n₁) (ap₀ (right ◯ g) r) ⟩
          ((pco ∘₀ p!gl n₁) ∘₀ pgl n₁) ∘₀ ap₀ (right ◯ g) r
            ≡⟨ ap (λ x → ((pco ∘₀ p!gl n₁) ∘₀ pgl n₁) ∘₀ x) $ ap₀-compose right g r ⟩
          ((pco ∘₀ p!gl n₁) ∘₀ pgl n₁) ∘₀ ap₀r (ap₀ g r)
            ≡⟨ ap (λ x → (x ∘₀ pgl n₁) ∘₀ ap₀r (ap₀ g r))
                  $ ! $ refl₀-right-unit $ pco ∘₀ p!gl n₁ ⟩∎
          (((pco ∘₀ p!gl n₁) ∘₀ refl₀) ∘₀ pgl n₁) ∘₀ ap₀r (ap₀ g r)
            ∎)

    bb⇒path : ∀ {b₂} → b-code-b b₁ b₂ → _≡₀_ {A = P} (right b₁) (right  b₂)
    bb⇒path = π₁ bp⇒path-split
    ba⇒path : ∀ {a₂} → b-code-a b₁ a₂ → _≡₀_ {A = P} (right b₁) (left a₂)
    ba⇒path = π₂ bp⇒path-split

    bp⇒path : ∀ {p₂ : P} → b-code b₁ p₂ → right b₁ ≡₀ p₂
    bp⇒path {p₂} = pushout-rec
      (λ p → b-code b₁ p → right b₁ ≡₀ p)
      (λ a → ba⇒path {a})
      (λ b → bb⇒path {b})
      (λ c → loc-fiber-rec l
        (λ c → transport (λ p → b-code b₁ p → right b₁ ≡₀ p) (glue c) ba⇒path
             ≡ bb⇒path)
        ⦃ λ c → →-is-set (π₀-is-set (right b₁ ≡ right (g c))) _ _ ⦄
        (λ n → funext λ co →
            transport (λ p → b-code b₁ p → right b₁ ≡₀ p) (glue $ loc n) ba⇒path co
                ≡⟨ trans-→ (b-code b₁) (λ x → right b₁ ≡₀ x) (glue $ loc n) ba⇒path co ⟩
            transport (λ p → right b₁ ≡₀ p) (glue $ loc n) (ba⇒path $ transport (b-code b₁) (! (glue $ loc n)) co)
                ≡⟨ ap (transport (λ p → right b₁ ≡₀ p) (glue $ loc n) ◯ ba⇒path) $ trans-b-code-!glue-loc n co ⟩
            transport (λ p → right b₁ ≡₀ p) (glue $ loc n) (ba⇒path $ bb⇒ba n co)
                ≡⟨ trans-cst≡₀id (glue $ loc n) (ba⇒path $ bb⇒ba n co) ⟩
            (ba⇒path $ bb⇒ba n co) ∘₀ pgl n
                ≡⟨ refl ⟩
            ((bb⇒path co ∘₀ p!gl n) ∘₀ refl₀) ∘₀ pgl n
                ≡⟨ ap (λ x → x ∘₀ pgl n) $ refl₀-right-unit $ bb⇒path co ∘₀ p!gl n ⟩
            (bb⇒path co ∘₀ p!gl n) ∘₀ pgl n
                ≡⟨ concat₀-assoc (bb⇒path co) (p!gl n) (pgl n) ⟩
            bb⇒path co ∘₀ (p!gl n ∘₀ pgl n)
                ≡⟨ ap (λ x → bb⇒path co ∘₀ proj x) $ opposite-left-inverse $ glue $ loc n ⟩
            bb⇒path co ∘₀ refl₀
                ≡⟨ refl₀-right-unit $ bb⇒path co ⟩∎
            bb⇒path co
                ∎)
        c)
      p₂

  module _ where

    private
      Lbaaa : ∀ n {a₂} → b-code-a (g $ loc n) a₂ → Set i
      Lbaaa n co = aa⇒path {f $ loc n} (ba⇒aa n co) ≡ pgl n ∘₀ ba⇒path co
      Lbbab : ∀ n {b₂} → b-code-b (g $ loc n) b₂ → Set i
      Lbbab n co = ab⇒path {f $ loc n} (bb⇒ab n co) ≡ pgl n ∘₀ bb⇒path co

    private
      bp⇒ap⇒path-split : ∀ n
        → (∀ {a₂} co → Lbbab n {a₂} co)
        × (∀ {b₂} co → Lbaaa n {b₂} co)
    abstract
      bp⇒ap⇒path-split n = b-code-rec (g $ loc n)
        (λ co → ab⇒path {f $ loc n} (bb⇒ab n co) ≡ pgl n ∘₀ bb⇒path co)
        ⦃ λ _ → ≡-is-set $ π₀-is-set _ ⦄
        (λ co → aa⇒path {f $ loc n} (ba⇒aa n co) ≡ pgl n ∘₀ ba⇒path co)
        ⦃ λ _ → ≡-is-set $ π₀-is-set _ ⦄
        (λ p →
          ab⇒path (bb⇒ab n (⟧b p))
            ≡⟨ refl ⟩
          (refl₀ ∘₀ pgl n) ∘₀ ap₀r p
            ≡⟨ ap (λ x → x ∘₀ ap₀r p) $ refl₀-left-unit $ pgl n ⟩
          pgl n ∘₀ ap₀r p
            ≡⟨ refl ⟩∎
          pgl n ∘₀ bb⇒path (⟧b p)
            ∎)
        (λ n₁ {co} eq p₁ →
          (aa⇒path (ba⇒aa n co) ∘₀ pgl n₁) ∘₀ ap₀r p₁
            ≡⟨ ap (λ x → (x ∘₀ pgl n₁) ∘₀ ap₀r p₁) eq ⟩
          ((pgl n ∘₀ ba⇒path co) ∘₀ pgl n₁) ∘₀ ap₀r p₁
            ≡⟨ ap (λ x → x ∘₀ ap₀r p₁)
                  $ concat₀-assoc (pgl n) (ba⇒path co) (pgl n₁) ⟩
          (pgl n ∘₀ (ba⇒path co ∘₀ pgl n₁)) ∘₀ ap₀r p₁
            ≡⟨ concat₀-assoc (pgl n) (ba⇒path co ∘₀ pgl n₁) (ap₀r p₁) ⟩∎
          pgl n ∘₀ ((ba⇒path co ∘₀ pgl n₁) ∘₀ ap₀r p₁)
            ∎)
        (λ n₁ {co} eq p₁ →
          (ab⇒path (bb⇒ab n co) ∘₀ p!gl n₁) ∘₀ ap₀l p₁
            ≡⟨ ap (λ x → (x ∘₀ p!gl n₁) ∘₀ ap₀l p₁) eq ⟩
          ((pgl n ∘₀ bb⇒path co) ∘₀ p!gl n₁) ∘₀ ap₀l p₁
            ≡⟨ ap (λ x → x ∘₀ ap₀l p₁)
                  $ concat₀-assoc (pgl n) (bb⇒path co) (p!gl n₁) ⟩
          (pgl n ∘₀ (bb⇒path co ∘₀ p!gl n₁)) ∘₀ ap₀l p₁
            ≡⟨ concat₀-assoc (pgl n) (bb⇒path co ∘₀ p!gl n₁) (ap₀l p₁) ⟩∎
          pgl n ∘₀ ((bb⇒path co ∘₀ p!gl n₁) ∘₀ ap₀l p₁)
            ∎)
        (λ _ co → prop-has-all-paths (π₀-is-set _ _ _) _ co)
        (λ _ co → prop-has-all-paths (π₀-is-set _ _ _) _ co)
        (λ _ _ _ _ → prop-has-all-paths (π₀-is-set _ _ _) _ _)

    ba⇒aa⇒path : ∀ n {a₂} co → Lbaaa n {a₂} co
    ba⇒aa⇒path n = π₂ $ bp⇒ap⇒path-split n
    bb⇒ab⇒path : ∀ n {b₂} co → Lbbab n {b₂} co
    bb⇒ab⇒path n = π₁ $ bp⇒ap⇒path-split n

    private
      bp⇒ap⇒path : ∀ n {p₂} (co : b-code (g $ loc n) p₂)
        → ap⇒path {f $ loc n} {p₂} (bp⇒ap n {p₂} co)
        ≡ pgl n ∘₀ bp⇒path {g $ loc n} {p₂} co
    abstract
      bp⇒ap⇒path n {p₂} = pushout-rec
        (λ x → ∀ (co : b-code (g $ loc n) x)
               → ap⇒path {f $ loc n} {x} (bp⇒ap n {x} co)
               ≡ pgl n ∘₀ bp⇒path {g $ loc n} {x} co)
        (λ a₂ → ba⇒aa⇒path n {a₂})
        (λ b₂ → bb⇒ab⇒path n {b₂})
        (λ _ → funext λ _ → prop-has-all-paths (π₀-is-set _ _ _) _ _)
        p₂

    code⇒path : ∀ {p₁ p₂} → code p₁ p₂ → p₁ ≡₀ p₂
    code⇒path {p₁} {p₂} = pushout-rec
      (λ p₁ → code p₁ p₂ → p₁ ≡₀ p₂)
      (λ a → ap⇒path {a} {p₂})
      (λ b → bp⇒path {b} {p₂})
      (loc-fiber-rec l
        (λ c → transport (λ x → code x p₂ → x ≡₀ p₂) (glue c) (ap⇒path {f c} {p₂})
             ≡ bp⇒path {g c} {p₂})
        ⦃ λ c → →-is-set (π₀-is-set (right (g c) ≡ p₂)) _ _ ⦄
        (λ n → funext λ (co : code (right $ g $ loc n) p₂) →
          transport (λ x → code x p₂ → x ≡₀ p₂) (glue $ loc n) (ap⇒path {f $ loc n} {p₂}) co
              ≡⟨ trans-→ (λ x → code x p₂) (λ x → x ≡₀ p₂) (glue $ loc n) (ap⇒path {f $ loc n} {p₂}) co ⟩
          transport (λ x → x ≡₀ p₂) (glue $ loc n) (ap⇒path {f $ loc n} {p₂}
            $ transport (λ x → code x p₂) (! (glue $ loc n)) co)
              ≡⟨ ap (transport (λ x → x ≡₀ p₂) (glue $ loc n) ◯ ap⇒path {f $ loc n} {p₂})
                    $ trans-!glue-code-loc n {p₂} co ⟩
          transport (λ x → x ≡₀ p₂) (glue $ loc n) (ap⇒path {f $ loc n} {p₂} $ bp⇒ap n {p₂} co)
              ≡⟨ ap (transport (λ x → x ≡₀ p₂) (glue $ loc n)) $ bp⇒ap⇒path n {p₂} co ⟩
          transport (λ x → x ≡₀ p₂) (glue $ loc n) (pgl n ∘₀ bp⇒path {g $ loc n} {p₂} co)
              ≡⟨ trans-id≡₀cst (glue $ loc n) (pgl n ∘₀ bp⇒path {g $ loc n} {p₂} co) ⟩
          p!gl n ∘₀ (pgl n ∘₀ bp⇒path {g $ loc n} {p₂} co)
              ≡⟨ ! $ concat₀-assoc (p!gl n) (pgl n) (bp⇒path {g $ loc n} {p₂} co) ⟩
          (p!gl n ∘₀ pgl n) ∘₀ bp⇒path {g $ loc n} {p₂} co
              ≡⟨ ap (λ x → proj x ∘₀ bp⇒path {g $ loc n} {p₂} co) $ opposite-left-inverse (glue $ loc n) ⟩
          refl₀ ∘₀ bp⇒path {g $ loc n} {p₂} co
              ≡⟨ refl₀-left-unit (bp⇒path {g $ loc n} {p₂} co) ⟩∎
          bp⇒path {g $ loc n} {p₂} co
              ∎))
      p₁
