{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Pushout

module Homotopy.VanKampen {i} (d : pushout-diag i) where
open pushout-diag d

open import Homotopy.Truncation
open import Homotopy.PathTruncation
open import Homotopy.VanKampen.Guide

module _ (l : legend i C) where
  open legend l

  open import Homotopy.VanKampen.Code d l
  open import Homotopy.VanKampen.CodeToPath d l

  private
    refl⇒code : ∀ p → code p p
    refl⇒code = pushout-rec
      (λ p → code p p)
      (λ _ → ⟧a refl₀)
      (λ _ → ⟧b refl₀)
      (loc-fiber-rec l
        (λ c → transport (λ p → code p p) (glue c) (⟧a refl₀)
             ≡ ⟧b refl₀)
        ⦃ λ _ → b-code-b-is-set _ _ _ _ ⦄
        (λ n →
          transport (λ p → code p p) (glue $ loc n) (⟧a refl₀)
              ≡⟨ trans-diag code (glue $ loc n) $ ⟧a refl₀ ⟩
          transport (λ p → code p (right $ g $ loc n)) (glue $ loc n)
            (transport (a-code (f $ loc n)) (glue $ loc n) (⟧a refl₀))
              ≡⟨ ap (transport (λ p → code p (right $ g $ loc n)) (glue $ loc n))
                    $ trans-a-code-glue-loc n $ ⟧a refl₀ ⟩
          transport (λ p → code p (right $ g $ loc n)) (glue $ loc n) (aa⇒ab n (⟧a refl₀))
              ≡⟨ trans-glue-code-loc n {right $ g $ loc n} $ aa⇒ab n (⟧a refl₀) ⟩
          ab⇒bb n (aa⇒ab n (⟧a refl₀))
              ≡⟨ refl ⟩
          ⟧b refl₀ bb⟦ n ⟧a refl₀ ba⟦ n ⟧b refl₀
              ≡⟨ b-code-b-refl-refl _ _ ⟩∎
          ⟧b refl₀
              ∎))


  path⇒code : ∀ {p₁} {p₂} (q : p₁ ≡₀ p₂) → code p₁ p₂
  path⇒code {p₁} {p₂} = π₀-extend-nondep
    ⦃ code-is-set p₁ p₂ ⦄
    (λ q → transport (code p₁) q (refl⇒code p₁))

  private
    refl⇒code⇒path : ∀ p → code⇒path (refl⇒code p) ≡ refl₀ {a = p}
    refl⇒code⇒path = pushout-rec
      (λ p → code⇒path (refl⇒code p) ≡ refl₀)
      (λ _ → refl)
      (λ _ → refl)
      (λ _ → prop-has-all-paths (π₀-is-set _ _ _) _ _)

    path′⇒code⇒path : ∀ {p₁ p₂} (q : p₁ ≡ p₂) → code⇒path (path⇒code $ proj q) ≡ proj q
    path′⇒code⇒path refl = refl⇒code⇒path _

  path⇒code⇒path : ∀ {p₁ p₂} (q : p₁ ≡₀ p₂) → code⇒path (path⇒code q) ≡ q
  path⇒code⇒path {p₁} {p₂} = π₀-extend
    ⦃ λ _ → ≡-is-set $ π₀-is-set (p₁ ≡ p₂) ⦄
    (path′⇒code⇒path {p₁} {p₂})

  private
    pgl : ∀ n → _≡₀_ {A = P} (left (f $ loc n)) (right (g $ loc n))
    pgl n = proj (glue $ loc n)

    p!gl : ∀ n → _≡₀_ {A = P} (right (g $ loc n)) (left (f $ loc n))
    p!gl n = proj (! (glue $ loc n))

    ap₀l : ∀ {a₁ a₂} → a₁ ≡₀ a₂ → _≡₀_ {A = P} (left a₁) (left a₂)
    ap₀l p = ap₀ left p

    ap₀r : ∀ {b₁ b₂} → b₁ ≡₀ b₂ → _≡₀_ {A = P} (right b₁) (right b₂)
    ap₀r p = ap₀ right p

  private
    path⇒code-concat₀ : ∀ {p₁ p₂ p₃} (q : p₁ ≡₀ p₂) (r : p₂ ≡ p₃)
      → path⇒code (q ∘₀ proj r) ≡ transport (code p₁) r (path⇒code q)
    path⇒code-concat₀ q refl = ap path⇒code $ refl₀-right-unit q

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
              ≡⟨ refl ⟩
            transport (a-code a₁) (ap left p) (path⇒code $ refl₀ {a = left a₁})
              ≡⟨ trans-ap (a-code a₁) left p $ ⟧a refl₀ ⟩
            transport (a-code-a a₁) p (⟧a refl₀)
              ≡⟨ trans-a-code-a p refl₀ ⟩∎
            ⟧a proj p
              ∎) p)
        (λ {a₂} n {co} eq p → π₀-extend
          {P = λ p → path⇒code (aa⇒path $ co ab⟦ n ⟧a p) ≡ co ab⟦ n ⟧a p}
          ⦃ λ _ → ≡-is-set $ a-code-a-is-set a₁ a₂ ⦄
          (λ p → let p′ = proj p in
            path⇒code ((ab⇒path co ∘₀ p!gl n) ∘₀ ap₀l p′)
                ≡⟨ path⇒code-concat₀ (ab⇒path co ∘₀ p!gl n) (ap left p) ⟩
            transport (a-code a₁) (ap left p) (path⇒code (ab⇒path co ∘₀ p!gl n))
                ≡⟨ trans-ap (a-code a₁) left p $ path⇒code $ ab⇒path co ∘₀ p!gl n ⟩
            transport (a-code-a a₁) p (path⇒code (ab⇒path co ∘₀ p!gl n))
                ≡⟨ ap (transport (a-code-a a₁) p)
                      $ path⇒code-concat₀ (ab⇒path co) (! (glue $ loc n)) ⟩
            transport (a-code-a a₁) p (transport (a-code a₁) (! (glue $ loc n))
              $ path⇒code $ ab⇒path co)
                ≡⟨ ap (transport (a-code-a a₁) p ◯ transport (a-code a₁) (! (glue $ loc n))) eq ⟩
            transport (a-code-a a₁) p (transport (a-code a₁) (! (glue $ loc n)) co)
                ≡⟨ ap (transport (a-code-a a₁) p) $ trans-a-code-!glue-loc n co ⟩
            transport (a-code-a a₁) p (co ab⟦ n ⟧a refl₀)
                ≡⟨ trans-a-code-ba p n co refl₀ ⟩∎
            co ab⟦ n ⟧a p′
                ∎) p)
        (λ {b₂} n {co} eq p → π₀-extend
          {P = λ p → path⇒code (ab⇒path $ co aa⟦ n ⟧b p) ≡ co aa⟦ n ⟧b p}
          ⦃ λ _ → ≡-is-set $ a-code-b-is-set a₁ b₂ ⦄
          (λ p → let p′ = proj p in
            path⇒code ((aa⇒path co ∘₀ pgl n) ∘₀ ap₀r p′)
                ≡⟨ path⇒code-concat₀ (aa⇒path co ∘₀ pgl n) (ap right p) ⟩
            transport (a-code a₁) (ap right p) (path⇒code (aa⇒path co ∘₀ pgl n))
                ≡⟨ trans-ap (a-code a₁) right p $ path⇒code $ aa⇒path co ∘₀ pgl n ⟩
            transport (a-code-b a₁) p (path⇒code (aa⇒path co ∘₀ pgl n))
                ≡⟨ ap (transport (a-code-b a₁) p)
                      $ path⇒code-concat₀ (aa⇒path co) (glue $ loc n) ⟩
            transport (a-code-b a₁) p (transport (a-code a₁) (glue $ loc n)
              $ path⇒code $ aa⇒path co)
                ≡⟨ ap (transport (a-code-b a₁) p ◯ transport (a-code a₁) (glue $ loc n)) eq ⟩
            transport (a-code-b a₁) p (transport (a-code a₁) (glue $ loc n) co)
                ≡⟨ ap (transport (a-code-b a₁) p) $ trans-a-code-glue-loc n co ⟩
            transport (a-code-b a₁) p (co aa⟦ n ⟧b refl₀)
                ≡⟨ trans-a-code-ab p n co refl₀ ⟩∎
            co aa⟦ n ⟧b p′
                ∎) p)
        (λ _ _ → prop-has-all-paths (a-code-a-is-set a₁ _ _ _) _ _)
        (λ _ _ → prop-has-all-paths (a-code-b-is-set a₁ _ _ _) _ _)
        (λ _ _ _ _ → prop-has-all-paths (a-code-a-is-set a₁ _ _ _) _ _)

      ap⇒path⇒ap : ∀ {p₂} (co : a-code a₁ p₂) → path⇒code {left a₁} {p₂} (ap⇒path co) ≡ co
      ap⇒path⇒ap {p₂} = pushout-rec
        (λ x → ∀ (co : a-code a₁ x) → path⇒code {left a₁} {x} (ap⇒path co) ≡ co)
        (λ _ → π₁ ap⇒path⇒ap-split)
        (λ _ → π₂ ap⇒path⇒ap-split)
        (λ _ → funext λ _ → prop-has-all-paths (a-code-b-is-set a₁ _ _ _) _ _)
        p₂

    -- FIXME Duplicate code!
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
              ≡⟨ refl ⟩
            transport (b-code b₁) (ap right p) (path⇒code $ refl₀ {a = right b₁})
              ≡⟨ trans-ap (b-code b₁) right p $ ⟧b refl₀ ⟩
            transport (b-code-b b₁) p (⟧b refl₀)
              ≡⟨ trans-b-code-b p refl₀ ⟩∎
            ⟧b proj p
              ∎) p)
        (λ {b₂} n {co} eq p → π₀-extend
          {P = λ p → path⇒code (bb⇒path $ co ba⟦ n ⟧b p) ≡ co ba⟦ n ⟧b p}
          ⦃ λ _ → ≡-is-set $ b-code-b-is-set b₁ b₂ ⦄
          (λ p → let p′ = proj p in
            path⇒code ((ba⇒path co ∘₀ pgl n) ∘₀ ap₀r p′)
                ≡⟨ path⇒code-concat₀ (ba⇒path co ∘₀ pgl n) (ap right p) ⟩
            transport (b-code b₁) (ap right p) (path⇒code (ba⇒path co ∘₀ pgl n))
                ≡⟨ trans-ap (b-code b₁) right p $ path⇒code $ ba⇒path co ∘₀ pgl n ⟩
            transport (b-code-b b₁) p (path⇒code (ba⇒path co ∘₀ pgl n))
                ≡⟨ ap (transport (b-code-b b₁) p)
                      $ path⇒code-concat₀ (ba⇒path co) (glue $ loc n) ⟩
            transport (b-code-b b₁) p (transport (b-code b₁) (glue $ loc n)
              $ path⇒code $ ba⇒path co)
                ≡⟨ ap (transport (b-code-b b₁) p ◯ transport (b-code b₁) (glue $ loc n)) eq ⟩
            transport (b-code-b b₁) p (transport (b-code b₁) (glue $ loc n) co)
                ≡⟨ ap (transport (b-code-b b₁) p) $ trans-b-code-glue-loc n co ⟩
            transport (b-code-b b₁) p (co ba⟦ n ⟧b refl₀)
                ≡⟨ trans-b-code-ab p n co refl₀ ⟩∎
            co ba⟦ n ⟧b p′
                ∎) p)
        (λ {a₂} n {co} eq p → π₀-extend
          {P = λ p → path⇒code (ba⇒path $ co bb⟦ n ⟧a p) ≡ co bb⟦ n ⟧a p}
          ⦃ λ _ → ≡-is-set $ b-code-a-is-set b₁ a₂ ⦄
          (λ p → let p′ = proj p in
            path⇒code ((bb⇒path co ∘₀ p!gl n) ∘₀ ap₀l p′)
                ≡⟨ path⇒code-concat₀ (bb⇒path co ∘₀ p!gl n) (ap left p) ⟩
            transport (b-code b₁) (ap left p) (path⇒code (bb⇒path co ∘₀ p!gl n))
                ≡⟨ trans-ap (b-code b₁) left p $ path⇒code $ bb⇒path co ∘₀ p!gl n ⟩
            transport (b-code-a b₁) p (path⇒code (bb⇒path co ∘₀ p!gl n))
                ≡⟨ ap (transport (b-code-a b₁) p)
                      $ path⇒code-concat₀ (bb⇒path co) (! (glue $ loc n)) ⟩
            transport (b-code-a b₁) p (transport (b-code b₁) (! (glue $ loc n))
              $ path⇒code $ bb⇒path co)
                ≡⟨ ap (transport (b-code-a b₁) p ◯ transport (b-code b₁) (! (glue $ loc n))) eq ⟩
            transport (b-code-a b₁) p (transport (b-code b₁) (! (glue $ loc n)) co)
                ≡⟨ ap (transport (b-code-a b₁) p) $ trans-b-code-!glue-loc n co ⟩
            transport (b-code-a b₁) p (co bb⟦ n ⟧a refl₀)
                ≡⟨ trans-b-code-ba p n co refl₀ ⟩∎
            co bb⟦ n ⟧a p′
                ∎) p)
        (λ _ _ → prop-has-all-paths (b-code-b-is-set b₁ _ _ _) _ _)
        (λ _ _ → prop-has-all-paths (b-code-a-is-set b₁ _ _ _) _ _)
        (λ _ _ _ _ → prop-has-all-paths (b-code-b-is-set b₁ _ _ _) _ _)

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

  van-kampen : ∀ {p₁ p₂} → (p₁ ≡₀ p₂) ≡ code p₁ p₂
  van-kampen {p₁} {p₂} =
    eq-to-path $ path⇒code {p₁} {p₂} ,
      iso-is-eq (path⇒code {p₁} {p₂}) (code⇒path {p₁} {p₂})
        (code⇒path⇒code {p₁} {p₂}) (path⇒code⇒path {p₁} {p₂})

module _ where
  open import Homotopy.VanKampen.Code d (id-legend C)

  naive-van-kampen : ∀ {p₁ p₂} → (p₁ ≡₀ p₂) ≡ code p₁ p₂
  naive-van-kampen = van-kampen (id-legend C)
