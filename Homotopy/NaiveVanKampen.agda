{-# OPTIONS --without-K #-}

open import Base

module Homotopy.NaiveVanKampen
  {i} (C A B : Set i)
  (f : C → A)
  (g : C → B) where

open import Homotopy.Pushout
open import Homotopy.Truncation
open import Spaces.Pi0Paths
open import Homotopy.NaiveVanKampen.Code C A B f g
open import Homotopy.NaiveVanKampen.CodeToPath C A B f g

private
  refl⇒code : ∀ p → code p p
  refl⇒code = pushout-rec
    (λ p → code p p)
    (λ _ → ⟧a refl₀ _)
    (λ _ → ⟧b refl₀ _)
    (λ c →
      transport (λ p → code p p) (glue c) (⟧a refl₀ (f c))
          ≡⟨ trans-2 code (glue c) $ ⟧a refl₀ (f c) ⟩
      transport (λ p → code p (right $ g c)) (glue c)
        (transport (a-code (f c)) (glue c) (⟧a refl₀ (f c)))
          ≡⟨ ap (transport (λ p → code p (right $ g c)) (glue c))
                $ trans-a-code-glue c $ ⟧a refl₀ (f c) ⟩
      transport (λ p → code p (right $ g c)) (glue c) (aa⇒ab c (⟧a refl₀ (f c)))
          ≡⟨ trans-glue-code c {right $ g c} $ aa⇒ab c (⟧a refl₀ (f c)) ⟩
      ab⇒bb c (aa⇒ab c (⟧a refl₀ (f c)))
          ≡⟨ refl _ ⟩
      ⟧b refl₀ (g c) bb⟦ c ⟧a refl₀ (f c) ba⟦ c ⟧b refl₀ (g c)
          ≡⟨ b-code-b-refl₀ _ _ _ ⟩∎
      ⟧b refl₀ (g c)
          ∎)

path⇒code : ∀ {p₁} {p₂} (q : p₁ ≡₀ p₂) → code p₁ p₂
path⇒code {p₁} {p₂} = π₀-extend-nondep
  ⦃ code-is-set p₁ p₂ ⦄
  (λ q → transport (code p₁) q (refl⇒code p₁))

private
  refl⇒code⇒path : ∀ p → code⇒path (refl⇒code p) ≡ refl₀ p
  refl⇒code⇒path = pushout-rec
    (λ p → code⇒path (refl⇒code p) ≡ refl₀ p)
    (λ _ → refl _)
    (λ _ → refl _)
    (λ _ → prop-has-all-paths (π₀-is-set _ _ _) _ _)

  path′⇒code⇒path : ∀ {p₁ p₂} (q : p₁ ≡ p₂) → code⇒path (path⇒code $ proj q) ≡ proj q
  path′⇒code⇒path (refl _) = refl⇒code⇒path _

path⇒code⇒path : ∀ {p₁ p₂} (q : p₁ ≡₀ p₂) → code⇒path (path⇒code q) ≡ q
path⇒code⇒path {p₁} {p₂} = π₀-extend
  ⦃ λ _ → ≡-is-set $ π₀-is-set (p₁ ≡ p₂) ⦄
  (path′⇒code⇒path {p₁} {p₂})

private
  pg : ∀ c → _≡₀_ {A = P} (left (f c)) (right (g c))
  pg c = proj (glue c)

  p!g : ∀ c → _≡₀_ {A = P} (right (g c)) (left (f c))
  p!g c = proj (! (glue c))

  ap₀l : ∀ {a₁ a₂} → a₁ ≡₀ a₂ → _≡₀_ {A = P} (left a₁) (left a₂)
  ap₀l p = ap₀ left p

  ap₀r : ∀ {b₁ b₂} → b₁ ≡₀ b₂ → _≡₀_ {A = P} (right b₁) (right b₂)
  ap₀r p = ap₀ right p

private
  path⇒code-concat₀ : ∀ {p₁ p₂ p₃} (q : p₁ ≡₀ p₂) (r : p₂ ≡ p₃)
    → path⇒code (q ∘₀ proj r) ≡ transport (code p₁) r (path⇒code q)
  path⇒code-concat₀ q (refl _) = ap path⇒code $ refl₀-right-unit q

  module _ {a₁} where
    ap⇒path⇒ap-split :
        (∀ {a₂} (co : a-code-a a₁ a₂) → path⇒code (aa⇒path co) ≡ co)
      × (∀ {b₂} (co : a-code-b a₁ b₂) → path⇒code (ab⇒path co) ≡ co)
    ap⇒path⇒ap-split = a-code-rec a₁
      (λ {a₂} (co : a-code-a a₁ a₂) → path⇒code (aa⇒path co) ≡ co)
      ⦃ λ {a₂} _ → ≡-is-set $ a-code-a-is-set a₁ a₂ ⦄
      (λ {b₂} (co : a-code-b a₁ b₂) → path⇒code (ab⇒path co) ≡ co)
      ⦃ λ {b₂} _ → ≡-is-set $ a-code-b-is-set a₁ b₂ ⦄
      (λ {a₂} p → π₀-extend
        {P = λ p → path⇒code (aa⇒path $ ⟧a p) ≡ ⟧a p}
        ⦃ λ _ → ≡-is-set $ a-code-a-is-set a₁ a₂ ⦄
        (λ p → let p′ = proj p in
          path⇒code (ap₀l p′)
            ≡⟨ refl _ ⟩
          transport (a-code a₁) (ap left p) (path⇒code $ refl₀ (left a₁))
            ≡⟨ trans-ap (a-code a₁) left p $ ⟧a refl₀ a₁ ⟩
          transport (a-code-a a₁) p (⟧a refl₀ a₁)
            ≡⟨ trans-a-code-a p $ refl₀ a₁ ⟩∎
          ⟧a proj p
            ∎) p)
      (λ {a₂} c {co} eq p → π₀-extend
        {P = λ p → path⇒code (aa⇒path $ co ab⟦ c ⟧a p) ≡ co ab⟦ c ⟧a p}
        ⦃ λ _ → ≡-is-set $ a-code-a-is-set a₁ a₂ ⦄
        (λ p → let p′ = proj p in
          path⇒code ((ab⇒path co ∘₀ p!g c) ∘₀ ap₀l p′)
              ≡⟨ path⇒code-concat₀ (ab⇒path co ∘₀ p!g c) (ap left p) ⟩
          transport (a-code a₁) (ap left p) (path⇒code (ab⇒path co ∘₀ p!g c))
              ≡⟨ trans-ap (a-code a₁) left p $ path⇒code $ ab⇒path co ∘₀ p!g c ⟩
          transport (a-code-a a₁) p (path⇒code (ab⇒path co ∘₀ p!g c))
              ≡⟨ ap (transport (a-code-a a₁) p)
                    $ path⇒code-concat₀ (ab⇒path co) (! (glue c)) ⟩
          transport (a-code-a a₁) p (transport (a-code a₁) (! (glue c))
            $ path⇒code $ ab⇒path co)
              ≡⟨ ap (transport (a-code-a a₁) p ◯ transport (a-code a₁) (! (glue c))) eq ⟩
          transport (a-code-a a₁) p (transport (a-code a₁) (! (glue c)) co)
              ≡⟨ ap (transport (a-code-a a₁) p) $ trans-a-code-!glue c co ⟩
          transport (a-code-a a₁) p (co ab⟦ c ⟧a refl₀ _)
              ≡⟨ trans-a-code-ba p c co (refl₀ _) ⟩∎
          co ab⟦ c ⟧a p′
              ∎) p)
      (λ {b₂} c {co} eq p → π₀-extend
        {P = λ p → path⇒code (ab⇒path $ co aa⟦ c ⟧b p) ≡ co aa⟦ c ⟧b p}
        ⦃ λ _ → ≡-is-set $ a-code-b-is-set a₁ b₂ ⦄
        (λ p → let p′ = proj p in
          path⇒code ((aa⇒path co ∘₀ pg c) ∘₀ ap₀r p′)
              ≡⟨ path⇒code-concat₀ (aa⇒path co ∘₀ pg c) (ap right p) ⟩
          transport (a-code a₁) (ap right p) (path⇒code (aa⇒path co ∘₀ pg c))
              ≡⟨ trans-ap (a-code a₁) right p $ path⇒code $ aa⇒path co ∘₀ pg c ⟩
          transport (a-code-b a₁) p (path⇒code (aa⇒path co ∘₀ pg c))
              ≡⟨ ap (transport (a-code-b a₁) p)
                    $ path⇒code-concat₀ (aa⇒path co) (glue c) ⟩
          transport (a-code-b a₁) p (transport (a-code a₁) (glue c)
            $ path⇒code $ aa⇒path co)
              ≡⟨ ap (transport (a-code-b a₁) p ◯ transport (a-code a₁) (glue c)) eq ⟩
          transport (a-code-b a₁) p (transport (a-code a₁) (glue c) co)
              ≡⟨ ap (transport (a-code-b a₁) p) $ trans-a-code-glue c co ⟩
          transport (a-code-b a₁) p (co aa⟦ c ⟧b refl₀ _)
              ≡⟨ trans-a-code-ab p c co (refl₀ _) ⟩∎
          co aa⟦ c ⟧b p′
              ∎) p)
      (λ _ _ _ → prop-has-all-paths (a-code-a-is-set a₁ _ _ _) _ _)
      (λ _ _ _ _ _ → prop-has-all-paths (a-code-a-is-set a₁ _ _ _) _ _)
      (λ _ _ _ _ _ → prop-has-all-paths (a-code-b-is-set a₁ _ _ _) _ _)

    ap⇒path⇒ap : ∀ {p₂} (co : a-code a₁ p₂) → path⇒code {left a₁} {p₂} (ap⇒path co) ≡ co
    ap⇒path⇒ap {p₂} = pushout-rec
      (λ x → ∀ (co : a-code a₁ x) → path⇒code {left a₁} {x} (ap⇒path co) ≡ co)
      (λ _ → π₁ ap⇒path⇒ap-split)
      (λ _ → π₂ ap⇒path⇒ap-split)
      (λ _ → funext λ _ → prop-has-all-paths (a-code-b-is-set a₁ _ _ _) _ _)
      p₂

  -- Unless there's a way to handle type-conversion nicely
  -- (with definitional equality), I'd rather copy and paste.
  module _ {b₁} where
    bp⇒path⇒bp-split :
        (∀ {b₂} (co : b-code-b b₁ b₂) → path⇒code (bb⇒path co) ≡ co)
      × (∀ {a₂} (co : b-code-a b₁ a₂) → path⇒code (ba⇒path co) ≡ co)
    bp⇒path⇒bp-split = b-code-rec b₁
      (λ {b₂} (co : b-code-b b₁ b₂) → path⇒code (bb⇒path co) ≡ co)
      ⦃ λ {b₂} _ → ≡-is-set $ b-code-b-is-set b₁ b₂ ⦄
      (λ {a₂} (co : b-code-a b₁ a₂) → path⇒code (ba⇒path co) ≡ co)
      ⦃ λ {a₂} _ → ≡-is-set $ b-code-a-is-set b₁ a₂ ⦄
      (λ {b₂} p → π₀-extend
        {P = λ p → path⇒code (bb⇒path $ ⟧b p) ≡ ⟧b p}
        ⦃ λ _ → ≡-is-set $ b-code-b-is-set b₁ b₂ ⦄
        (λ p → let p′ = proj p in
          path⇒code (ap₀r p′)
            ≡⟨ refl _ ⟩
          transport (b-code b₁) (ap right p) (path⇒code $ refl₀ (right b₁))
            ≡⟨ trans-ap (b-code b₁) right p $ ⟧b refl₀ b₁ ⟩
          transport (b-code-b b₁) p (⟧b refl₀ b₁)
            ≡⟨ trans-b-code-b p $ refl₀ b₁ ⟩∎
          ⟧b proj p
            ∎) p)
      (λ {b₂} c {co} eq p → π₀-extend
        {P = λ p → path⇒code (bb⇒path $ co ba⟦ c ⟧b p) ≡ co ba⟦ c ⟧b p}
        ⦃ λ _ → ≡-is-set $ b-code-b-is-set b₁ b₂ ⦄
        (λ p → let p′ = proj p in
          path⇒code ((ba⇒path co ∘₀ pg c) ∘₀ ap₀r p′)
              ≡⟨ path⇒code-concat₀ (ba⇒path co ∘₀ pg c) (ap right p) ⟩
          transport (b-code b₁) (ap right p) (path⇒code (ba⇒path co ∘₀ pg c))
              ≡⟨ trans-ap (b-code b₁) right p $ path⇒code $ ba⇒path co ∘₀ pg c ⟩
          transport (b-code-b b₁) p (path⇒code (ba⇒path co ∘₀ pg c))
              ≡⟨ ap (transport (b-code-b b₁) p)
                    $ path⇒code-concat₀ (ba⇒path co) (glue c) ⟩
          transport (b-code-b b₁) p (transport (b-code b₁) (glue c)
            $ path⇒code $ ba⇒path co)
              ≡⟨ ap (transport (b-code-b b₁) p ◯ transport (b-code b₁) (glue c)) eq ⟩
          transport (b-code-b b₁) p (transport (b-code b₁) (glue c) co)
              ≡⟨ ap (transport (b-code-b b₁) p) $ trans-b-code-glue c co ⟩
          transport (b-code-b b₁) p (co ba⟦ c ⟧b refl₀ _)
              ≡⟨ trans-b-code-ab p c co (refl₀ _) ⟩∎
          co ba⟦ c ⟧b p′
              ∎) p)
      (λ {a₂} c {co} eq p → π₀-extend
        {P = λ p → path⇒code (ba⇒path $ co bb⟦ c ⟧a p) ≡ co bb⟦ c ⟧a p}
        ⦃ λ _ → ≡-is-set $ b-code-a-is-set b₁ a₂ ⦄
        (λ p → let p′ = proj p in
          path⇒code ((bb⇒path co ∘₀ p!g c) ∘₀ ap₀l p′)
              ≡⟨ path⇒code-concat₀ (bb⇒path co ∘₀ p!g c) (ap left p) ⟩
          transport (b-code b₁) (ap left p) (path⇒code (bb⇒path co ∘₀ p!g c))
              ≡⟨ trans-ap (b-code b₁) left p $ path⇒code $ bb⇒path co ∘₀ p!g c ⟩
          transport (b-code-a b₁) p (path⇒code (bb⇒path co ∘₀ p!g c))
              ≡⟨ ap (transport (b-code-a b₁) p)
                    $ path⇒code-concat₀ (bb⇒path co) (! (glue c)) ⟩
          transport (b-code-a b₁) p (transport (b-code b₁) (! (glue c))
            $ path⇒code $ bb⇒path co)
              ≡⟨ ap (transport (b-code-a b₁) p ◯ transport (b-code b₁) (! (glue c))) eq ⟩
          transport (b-code-a b₁) p (transport (b-code b₁) (! (glue c)) co)
              ≡⟨ ap (transport (b-code-a b₁) p) $ trans-b-code-!glue c co ⟩
          transport (b-code-a b₁) p (co bb⟦ c ⟧a refl₀ _)
              ≡⟨ trans-b-code-ba p c co (refl₀ _) ⟩∎
          co bb⟦ c ⟧a p′
              ∎) p)
      (λ _ _ _ → prop-has-all-paths (b-code-b-is-set b₁ _ _ _) _ _)
      (λ _ _ _ _ _ → prop-has-all-paths (b-code-b-is-set b₁ _ _ _) _ _)
      (λ _ _ _ _ _ → prop-has-all-paths (b-code-a-is-set b₁ _ _ _) _ _)

    bp⇒path⇒bp : ∀ {p₂} (co : b-code b₁ p₂) → path⇒code {right b₁} {p₂} (bp⇒path co) ≡ co
    bp⇒path⇒bp {p₂} = pushout-rec
      (λ x → ∀ (co : b-code b₁ x) → path⇒code {right b₁} {x} (bp⇒path co) ≡ co)
      (λ _ → π₂ bp⇒path⇒bp-split)
      (λ _ → π₁ bp⇒path⇒bp-split)
      (λ _ → funext λ _ → prop-has-all-paths (b-code-b-is-set b₁ _ _ _) _ _)
      p₂

code⇒path⇒code : ∀ {p₁ p₂} (co : code p₁ p₂) → path⇒code {p₁} {p₂} (code⇒path co) ≡ co
code⇒path⇒code {p₁} {p₂} = pushout-rec
  (λ p₁ → ∀ (co : code p₁ p₂) → path⇒code {p₁} {p₂} (code⇒path co) ≡ co)
  (λ a₁ → ap⇒path⇒ap {a₁} {p₂})
  (λ b₁ → bp⇒path⇒bp {b₁} {p₂})
  (λ c → funext λ co → prop-has-all-paths (b-code-is-set (g c) p₂ _ co) _ _)
  p₁

naive-van-kampen : ∀ {p₁ p₂} → (p₁ ≡₀ p₂) ≡ code p₁ p₂
naive-van-kampen {p₁} {p₂} =
  eq-to-path $ path⇒code {p₁} {p₂} ,
    iso-is-eq (path⇒code {p₁} {p₂}) (code⇒path {p₁} {p₂})
      (code⇒path⇒code {p₁} {p₂}) (path⇒code⇒path {p₁} {p₂})
